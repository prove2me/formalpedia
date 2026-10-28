-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1121_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:34.945098+00:00
-- url     : https://prove2.me/submissions/dd00c489-af15-4ce5-8f9f-844b9f919199

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1121_s0_0 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898475009/10000000000 : ℝ)*x 0 + (6059196519/10000000000 : ℝ)*x 1 + (2388905359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898475009/10000000000 : ℝ)^4157 ≤ (11029513824063/100000000000000 : ℝ)^3133 := by
    have hnat : (1898475009 : ℕ)^4157*100000000000000^3133 ≤ 11029513824063^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898475009 10000000000 11029513824063 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6059196519/10000000000 : ℝ)^4157 ≤ (51439750736603/100000000000000 : ℝ)^3133 := by
    have hnat : (6059196519 : ℕ)^4157*100000000000000^3133 ≤ 51439750736603^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6059196519 10000000000 51439750736603 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388905359/5000000000 : ℝ)^4157 ≤ (18765367716621/50000000000000 : ℝ)^3133 := by
    have hnat : (2388905359 : ℕ)^4157*50000000000000^3133 ≤ 18765367716621^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388905359 5000000000 18765367716621 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898475009/10000000000 : ℝ), (6059196519/10000000000 : ℝ), (2388905359/5000000000 : ℝ)] ![(11029513824063/100000000000000 : ℝ), (51439750736603/100000000000000 : ℝ), (18765367716621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898475009/10000000000 : ℝ)|^4157 ≤ (11029513824063/100000000000000 : ℝ)^3133
        have hw : |(-1898475009/10000000000 : ℝ)|=(1898475009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6059196519/10000000000 : ℝ)|^4157 ≤ (51439750736603/100000000000000 : ℝ)^3133
        have hw : |(6059196519/10000000000 : ℝ)|=(6059196519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388905359/5000000000 : ℝ)|^4157 ≤ (18765367716621/50000000000000 : ℝ)^3133
        have hw : |(2388905359/5000000000 : ℝ)|=(2388905359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_1 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2758988239/5000000000 : ℝ)*x 0 + (-1317222511/5000000000 : ℝ)*x 1 + (74653293/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758988239/5000000000 : ℝ)^4157 ≤ (9086828211947/20000000000000 : ℝ)^3133 := by
    have hnat : (2758988239 : ℕ)^4157*20000000000000^3133 ≤ 9086828211947^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758988239 5000000000 9086828211947 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317222511/5000000000 : ℝ)^4157 ≤ (851756157191/5000000000000 : ℝ)^3133 := by
    have hnat : (1317222511 : ℕ)^4157*5000000000000^3133 ≤ 851756157191^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317222511 5000000000 851756157191 5000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74653293/156250000 : ℝ)^4157 ≤ (9382683946903/25000000000000 : ℝ)^3133 := by
    have hnat : (74653293 : ℕ)^4157*25000000000000^3133 ≤ 9382683946903^3133*156250000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74653293 156250000 9382683946903 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758988239/5000000000 : ℝ), (-1317222511/5000000000 : ℝ), (74653293/156250000 : ℝ)] ![(9086828211947/20000000000000 : ℝ), (851756157191/5000000000000 : ℝ), (9382683946903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758988239/5000000000 : ℝ)|^4157 ≤ (9086828211947/20000000000000 : ℝ)^3133
        have hw : |(2758988239/5000000000 : ℝ)|=(2758988239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1317222511/5000000000 : ℝ)|^4157 ≤ (851756157191/5000000000000 : ℝ)^3133
        have hw : |(-1317222511/5000000000 : ℝ)|=(1317222511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74653293/156250000 : ℝ)|^4157 ≤ (9382683946903/25000000000000 : ℝ)^3133
        have hw : |(74653293/156250000 : ℝ)|=(74653293/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_2 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5517976629/10000000000 : ℝ)*x 0 + (298613163/625000000 : ℝ)*x 1 + (-658611251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517976629/10000000000 : ℝ)^4157 ≤ (11358535677353/25000000000000 : ℝ)^3133 := by
    have hnat : (5517976629 : ℕ)^4157*25000000000000^3133 ≤ 11358535677353^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517976629 10000000000 11358535677353 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298613163/625000000 : ℝ)^4157 ≤ (1172835446461/3125000000000 : ℝ)^3133 := by
    have hnat : (298613163 : ℕ)^4157*3125000000000^3133 ≤ 1172835446461^3133*625000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298613163 625000000 1172835446461 3125000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658611251/2500000000 : ℝ)^4157 ≤ (2129390373673/12500000000000 : ℝ)^3133 := by
    have hnat : (658611251 : ℕ)^4157*12500000000000^3133 ≤ 2129390373673^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658611251 2500000000 2129390373673 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517976629/10000000000 : ℝ), (298613163/625000000 : ℝ), (-658611251/2500000000 : ℝ)] ![(11358535677353/25000000000000 : ℝ), (1172835446461/3125000000000 : ℝ), (2129390373673/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517976629/10000000000 : ℝ)|^4157 ≤ (11358535677353/25000000000000 : ℝ)^3133
        have hw : |(5517976629/10000000000 : ℝ)|=(5517976629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(298613163/625000000 : ℝ)|^4157 ≤ (1172835446461/3125000000000 : ℝ)^3133
        have hw : |(298613163/625000000 : ℝ)|=(298613163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658611251/2500000000 : ℝ)|^4157 ≤ (2129390373673/12500000000000 : ℝ)^3133
        have hw : |(-658611251/2500000000 : ℝ)|=(658611251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_3 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210134737/500000000 : ℝ)*x 0 + (3122071423/10000000000 : ℝ)*x 1 + (1132171871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210134737/500000000 : ℝ)^4157 ≤ (791444492327/2500000000000 : ℝ)^3133 := by
    have hnat : (210134737 : ℕ)^4157*2500000000000^3133 ≤ 791444492327^3133*500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210134737 500000000 791444492327 2500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122071423/10000000000 : ℝ)^4157 ≤ (5335128447137/25000000000000 : ℝ)^3133 := by
    have hnat : (3122071423 : ℕ)^4157*25000000000000^3133 ≤ 5335128447137^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122071423 10000000000 5335128447137 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132171871/2000000000 : ℝ)^4157 ≤ (47001706496259/100000000000000 : ℝ)^3133 := by
    have hnat : (1132171871 : ℕ)^4157*100000000000000^3133 ≤ 47001706496259^3133*2000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132171871 2000000000 47001706496259 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210134737/500000000 : ℝ), (3122071423/10000000000 : ℝ), (1132171871/2000000000 : ℝ)] ![(791444492327/2500000000000 : ℝ), (5335128447137/25000000000000 : ℝ), (47001706496259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210134737/500000000 : ℝ)|^4157 ≤ (791444492327/2500000000000 : ℝ)^3133
        have hw : |(210134737/500000000 : ℝ)|=(210134737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122071423/10000000000 : ℝ)|^4157 ≤ (5335128447137/25000000000000 : ℝ)^3133
        have hw : |(3122071423/10000000000 : ℝ)|=(3122071423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132171871/2000000000 : ℝ)|^4157 ≤ (47001706496259/100000000000000 : ℝ)^3133
        have hw : |(1132171871/2000000000 : ℝ)|=(1132171871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_4 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1903683953/10000000000 : ℝ)*x 0 + (4810877527/10000000000 : ℝ)*x 1 + (301248397/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1903683953/10000000000 : ℝ)^4157 ≤ (22139370153/200000000000 : ℝ)^3133 := by
    have hnat : (1903683953 : ℕ)^4157*200000000000^3133 ≤ 22139370153^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903683953 10000000000 22139370153 200000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810877527/10000000000 : ℝ)^4157 ≤ (37875768097897/100000000000000 : ℝ)^3133 := by
    have hnat : (4810877527 : ℕ)^4157*100000000000000^3133 ≤ 37875768097897^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810877527 10000000000 37875768097897 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301248397/500000000 : ℝ)^4157 ≤ (10210909364341/20000000000000 : ℝ)^3133 := by
    have hnat : (301248397 : ℕ)^4157*20000000000000^3133 ≤ 10210909364341^3133*500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301248397 500000000 10210909364341 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1903683953/10000000000 : ℝ), (4810877527/10000000000 : ℝ), (301248397/500000000 : ℝ)] ![(22139370153/200000000000 : ℝ), (37875768097897/100000000000000 : ℝ), (10210909364341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1903683953/10000000000 : ℝ)|^4157 ≤ (22139370153/200000000000 : ℝ)^3133
        have hw : |(-1903683953/10000000000 : ℝ)|=(1903683953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810877527/10000000000 : ℝ)|^4157 ≤ (37875768097897/100000000000000 : ℝ)^3133
        have hw : |(4810877527/10000000000 : ℝ)|=(4810877527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(301248397/500000000 : ℝ)|^4157 ≤ (10210909364341/20000000000000 : ℝ)^3133
        have hw : |(301248397/500000000 : ℝ)|=(301248397/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_5 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646237103/1250000000 : ℝ)*x 0 + (-1387288563/10000000000 : ℝ)*x 1 + (240998859/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646237103/1250000000 : ℝ)^4157 ≤ (41671137169463/100000000000000 : ℝ)^3133 := by
    have hnat : (646237103 : ℕ)^4157*100000000000000^3133 ≤ 41671137169463^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646237103 1250000000 41671137169463 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387288563/10000000000 : ℝ)^4157 ≤ (727427625173/10000000000000 : ℝ)^3133 := by
    have hnat : (1387288563 : ℕ)^4157*10000000000000^3133 ≤ 727427625173^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387288563 10000000000 727427625173 10000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240998859/400000000 : ℝ)^4157 ≤ (51054586567279/100000000000000 : ℝ)^3133 := by
    have hnat : (240998859 : ℕ)^4157*100000000000000^3133 ≤ 51054586567279^3133*400000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240998859 400000000 51054586567279 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646237103/1250000000 : ℝ), (-1387288563/10000000000 : ℝ), (240998859/400000000 : ℝ)] ![(41671137169463/100000000000000 : ℝ), (727427625173/10000000000000 : ℝ), (51054586567279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646237103/1250000000 : ℝ)|^4157 ≤ (41671137169463/100000000000000 : ℝ)^3133
        have hw : |(646237103/1250000000 : ℝ)|=(646237103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387288563/10000000000 : ℝ)|^4157 ≤ (727427625173/10000000000000 : ℝ)^3133
        have hw : |(-1387288563/10000000000 : ℝ)|=(1387288563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240998859/400000000 : ℝ)|^4157 ≤ (51054586567279/100000000000000 : ℝ)^3133
        have hw : |(240998859/400000000 : ℝ)|=(240998859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_6 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20194927/39062500 : ℝ)*x 0 + (6024968293/10000000000 : ℝ)*x 1 + (-693643403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20194927/39062500 : ℝ)^4157 ≤ (41671185167781/100000000000000 : ℝ)^3133 := by
    have hnat : (20194927 : ℕ)^4157*100000000000000^3133 ≤ 41671185167781^3133*39062500^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20194927 39062500 41671185167781 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6024968293/10000000000 : ℝ)^4157 ≤ (51054550790641/100000000000000 : ℝ)^3133 := by
    have hnat : (6024968293 : ℕ)^4157*100000000000000^3133 ≤ 51054550790641^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024968293 10000000000 51054550790641 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693643403/5000000000 : ℝ)^4157 ≤ (7274264027703/100000000000000 : ℝ)^3133 := by
    have hnat : (693643403 : ℕ)^4157*100000000000000^3133 ≤ 7274264027703^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693643403 5000000000 7274264027703 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20194927/39062500 : ℝ), (6024968293/10000000000 : ℝ), (-693643403/5000000000 : ℝ)] ![(41671185167781/100000000000000 : ℝ), (51054550790641/100000000000000 : ℝ), (7274264027703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20194927/39062500 : ℝ)|^4157 ≤ (41671185167781/100000000000000 : ℝ)^3133
        have hw : |(20194927/39062500 : ℝ)|=(20194927/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6024968293/10000000000 : ℝ)|^4157 ≤ (51054550790641/100000000000000 : ℝ)^3133
        have hw : |(6024968293/10000000000 : ℝ)|=(6024968293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-693643403/5000000000 : ℝ)|^4157 ≤ (7274264027703/100000000000000 : ℝ)^3133
        have hw : |(-693643403/5000000000 : ℝ)|=(693643403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s0_7 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213011517/10000000000 : ℝ)*x 0 + (5595348453/10000000000 : ℝ)*x 1 + (3189883243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213011517/10000000000 : ℝ)^4157 ≤ (15880467357181/50000000000000 : ℝ)^3133 := by
    have hnat : (4213011517 : ℕ)^4157*50000000000000^3133 ≤ 15880467357181^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213011517 10000000000 15880467357181 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595348453/10000000000 : ℝ)^4157 ≤ (46281362068287/100000000000000 : ℝ)^3133 := by
    have hnat : (5595348453 : ℕ)^4157*100000000000000^3133 ≤ 46281362068287^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595348453 10000000000 46281362068287 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189883243/10000000000 : ℝ)^4157 ≤ (5489425799191/25000000000000 : ℝ)^3133 := by
    have hnat : (3189883243 : ℕ)^4157*25000000000000^3133 ≤ 5489425799191^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189883243 10000000000 5489425799191 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213011517/10000000000 : ℝ), (5595348453/10000000000 : ℝ), (3189883243/10000000000 : ℝ)] ![(15880467357181/50000000000000 : ℝ), (46281362068287/100000000000000 : ℝ), (5489425799191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213011517/10000000000 : ℝ)|^4157 ≤ (15880467357181/50000000000000 : ℝ)^3133
        have hw : |(4213011517/10000000000 : ℝ)|=(4213011517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595348453/10000000000 : ℝ)|^4157 ≤ (46281362068287/100000000000000 : ℝ)^3133
        have hw : |(5595348453/10000000000 : ℝ)|=(5595348453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189883243/10000000000 : ℝ)|^4157 ≤ (5489425799191/25000000000000 : ℝ)^3133
        have hw : |(3189883243/10000000000 : ℝ)|=(3189883243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1121_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (327/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3487/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (8313/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8313 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8313*1^2048 ≤ 0^2048*1^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8313/2048 : ℝ) ≤ (2425095586768657731/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8313 ≤ (2425095586768657731/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8313*100000000000000000000^2048 ≤ 2425095586768657731^2048*5^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2425095586768657731 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2425095586768657731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8313 := by
      have hnat : (1 : ℕ)^2048*1^8313 ≤ 1^8313*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102425095586768657731/100000000000000000000 : ℝ) ≤ (5029603288175267/5000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (102425095586768657731/100000000000000000000 : ℝ)^2048 ≤ (5029603288175267/5000000000000000 : ℝ)^8313 := by
      have hnat : (102425095586768657731 : ℕ)^2048*5000000000000000^8313 ≤ 5029603288175267^8313*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102425095586768657731 100000000000000000000 5029603288175267 5000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029603288175267/5000000000000000 : ℝ)) (X := (102425095586768657731/100000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52425095586768657731/50000000000000000000 : ℝ) ≤ (2529603288175267/2500000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (52425095586768657731/50000000000000000000 : ℝ)^2048 ≤ (2529603288175267/2500000000000000 : ℝ)^8313 := by
      have hnat : (52425095586768657731 : ℕ)^2048*2500000000000000^8313 ≤ 2529603288175267^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52425095586768657731 50000000000000000000 2529603288175267 2500000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529603288175267/2500000000000000 : ℝ)) (X := (52425095586768657731/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29603288175267/2000000000000000 : ℝ)*(0 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29603288175267/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2425095586768657731/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29603288175267/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8313/2048 : ℝ) := by
    rw [show (1 : ℝ)+(29603288175267/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029603288175267/5000000000000000 : ℝ) by norm_num, show 1+(2425095586768657731/100000000000000000000 : ℝ)+(0 : ℝ)=(102425095586768657731/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2425095586768657731/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29603288175267/2000000000000000 : ℝ)*(2/5 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29603288175267/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529603288175267/2500000000000000 : ℝ) by norm_num, show 1+2*(2425095586768657731/100000000000000000000 : ℝ)=(52425095586768657731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29603288175267/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29603288175267/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29603288175267/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29603288175267/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29603288175267/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29603288175267/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1898475009/10000000000 : ℝ)*X 0 0+(6059196519/10000000000 : ℝ)*X 0 1+(2388905359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2758988239/5000000000 : ℝ)*X 1 0+(-1317222511/5000000000 : ℝ)*X 1 1+(74653293/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517976629/10000000000 : ℝ)*X 2 0+(298613163/625000000 : ℝ)*X 2 1+(-658611251/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((210134737/500000000 : ℝ)*X 0 0+(3122071423/10000000000 : ℝ)*X 0 1+(1132171871/2000000000 : ℝ)*X 0 2+(210134737/500000000 : ℝ)*X 1 0+(3122071423/10000000000 : ℝ)*X 1 1+(1132171871/2000000000 : ℝ)*X 1 2+(210134737/500000000 : ℝ)*X 2 0+(3122071423/10000000000 : ℝ)*X 2 1+(1132171871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1903683953/10000000000 : ℝ)*X 0 0+(4810877527/10000000000 : ℝ)*X 0 1+(301248397/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646237103/1250000000 : ℝ)*X 1 0+(-1387288563/10000000000 : ℝ)*X 1 1+(240998859/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20194927/39062500 : ℝ)*X 2 0+(6024968293/10000000000 : ℝ)*X 2 1+(-693643403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213011517/10000000000 : ℝ)*X 0 0+(5595348453/10000000000 : ℝ)*X 0 1+(3189883243/10000000000 : ℝ)*X 0 2+(4213011517/10000000000 : ℝ)*X 1 0+(5595348453/10000000000 : ℝ)*X 1 1+(3189883243/10000000000 : ℝ)*X 1 2+(4213011517/10000000000 : ℝ)*X 2 0+(5595348453/10000000000 : ℝ)*X 2 1+(3189883243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35370664092376604824737/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34755851/100000000000000 : ℝ)*(base1) + (34690697/5000000000000 : ℝ)*(base19) + (165675869/25000000000000 : ℝ)*(base23) + (52466413/100000000000000 : ℝ)*(base24) + (163312299/100000000000000 : ℝ)*(upper3) + (146787453447363/25000000000000 : ℝ)*(major0) + (146787453447363/25000000000000 : ℝ)*(major1) + (146787453447363/25000000000000 : ℝ)*(major2) + (97550919904487/12500000000000 : ℝ)*(sp0) + (780408114506071/100000000000000 : ℝ)*(sp1) + (390204046575061/50000000000000 : ℝ)*(sp2) + (393889454498853/100000000000000 : ℝ)*(sp3) + (741919983/50000000000000 : ℝ)*(sp4) + (247136481/20000000000000 : ℝ)*(sp7) + (98472681234277/25000000000000 : ℝ)*(f.failure) + (195102202080003/25000000000000 : ℝ)*(f.sum) + (35477170604079/25000000000000000000000000000 : ℝ)*base66 + (146806033470921/50000000000000000000000000000 : ℝ)*base67 + (393278773070921/50000000000000000000000000000 : ℝ)*base69 + (235103425820921/50000000000000000000000000000 : ℝ)*base71 + (29140065079079/25000000000000000000000000000 : ℝ)*base74 + (405616171870921/50000000000000000000000000000 : ℝ)*base75 + (344188385820921/50000000000000000000000000000 : ℝ)*base77 + (377245829970921/50000000000000000000000000000 : ℝ)*base79 + (108923684420921/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11470887/1250000000000000000000 : ℝ)*base90 + (11470887/1250000000000000000000 : ℝ)*base92 + (11470887/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10208276378867157363339/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (267212607/50000000000000 : ℝ)*(base19) + (911185029/50000000000000 : ℝ)*(base23) + (257907531/50000000000000 : ℝ)*(base39) + (30038207/12500000000000 : ℝ)*(upper3) + (27819643/10000000000000 : ℝ)*(upper5) + (19365309051153/3125000000000 : ℝ)*(major0) + (19365309051153/3125000000000 : ℝ)*(major1) + (309844686910917/50000000000000 : ℝ)*(major2) + (105557067/5000000000000 : ℝ)*(sp1) + (635753899/20000000000000 : ℝ)*(sp2) + (411829370174147/50000000000000 : ℝ)*(sp4) + (823656094781741/100000000000000 : ℝ)*(sp5) + (823654255023803/100000000000000 : ℝ)*(sp6) + (415720305333867/100000000000000 : ℝ)*(sp7) + (415720305333867/100000000000000 : ℝ)*(f.failure) + (823659256163357/100000000000000 : ℝ)*(f.sum) + (51081115016909/20000000000000000000000000000 : ℝ)*base66 + (42601242789839/100000000000000000000000000000 : ℝ)*base67 + (3316375926601/6250000000000000000000000000 : ℝ)*base69 + (727327822610161/100000000000000000000000000000 : ℝ)*base72 + (30666884363091/20000000000000000000000000000 : ℝ)*base73 + (17532569667149/6250000000000000000000000000 : ℝ)*base76 + (826268379649/6250000000000000000000000000 : ℝ)*base78 + (19862288745351/6250000000000000000000000000 : ℝ)*base79 + (4233971956631/781250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (43280823/5000000000000000000000 : ℝ)*base89 + (43280823/5000000000000000000000 : ℝ)*base91 + (43280823/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1121_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (327/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3487/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1121_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1121_s1_0 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052326593/5000000000 : ℝ)*x 0 + (1426790417/2500000000 : ℝ)*x 1 + (1249460401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052326593/5000000000 : ℝ)^4157 ≤ (31615980647/250000000000 : ℝ)^3133 := by
    have hnat : (1052326593 : ℕ)^4157*250000000000^3133 ≤ 31615980647^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052326593 5000000000 31615980647 250000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426790417/2500000000 : ℝ)^4157 ≤ (11878121259929/25000000000000 : ℝ)^3133 := by
    have hnat : (1426790417 : ℕ)^4157*25000000000000^3133 ≤ 11878121259929^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426790417 2500000000 11878121259929 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249460401/2500000000 : ℝ)^4157 ≤ (19920561344637/50000000000000 : ℝ)^3133 := by
    have hnat : (1249460401 : ℕ)^4157*50000000000000^3133 ≤ 19920561344637^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249460401 2500000000 19920561344637 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052326593/5000000000 : ℝ), (1426790417/2500000000 : ℝ), (1249460401/2500000000 : ℝ)] ![(31615980647/250000000000 : ℝ), (11878121259929/25000000000000 : ℝ), (19920561344637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052326593/5000000000 : ℝ)|^4157 ≤ (31615980647/250000000000 : ℝ)^3133
        have hw : |(-1052326593/5000000000 : ℝ)|=(1052326593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426790417/2500000000 : ℝ)|^4157 ≤ (11878121259929/25000000000000 : ℝ)^3133
        have hw : |(1426790417/2500000000 : ℝ)|=(1426790417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249460401/2500000000 : ℝ)|^4157 ≤ (19920561344637/50000000000000 : ℝ)^3133
        have hw : |(1249460401/2500000000 : ℝ)|=(1249460401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_1 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420278737/10000000000 : ℝ)*x 0 + (-49757077/200000000 : ℝ)*x 1 + (4997841371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420278737/10000000000 : ℝ)^4157 ≤ (22184946142627/50000000000000 : ℝ)^3133 := by
    have hnat : (5420278737 : ℕ)^4157*50000000000000^3133 ≤ 22184946142627^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420278737 10000000000 22184946142627 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49757077/200000000 : ℝ)^4157 ≤ (1578898746971/10000000000000 : ℝ)^3133 := by
    have hnat : (49757077 : ℕ)^4157*10000000000000^3133 ≤ 1578898746971^3133*200000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49757077 200000000 1578898746971 10000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4997841371/10000000000 : ℝ)^4157 ≤ (39841120224797/100000000000000 : ℝ)^3133 := by
    have hnat : (4997841371 : ℕ)^4157*100000000000000^3133 ≤ 39841120224797^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997841371 10000000000 39841120224797 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420278737/10000000000 : ℝ), (-49757077/200000000 : ℝ), (4997841371/10000000000 : ℝ)] ![(22184946142627/50000000000000 : ℝ), (1578898746971/10000000000000 : ℝ), (39841120224797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420278737/10000000000 : ℝ)|^4157 ≤ (22184946142627/50000000000000 : ℝ)^3133
        have hw : |(5420278737/10000000000 : ℝ)|=(5420278737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49757077/200000000 : ℝ)|^4157 ≤ (1578898746971/10000000000000 : ℝ)^3133
        have hw : |(-49757077/200000000 : ℝ)|=(49757077/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4997841371/10000000000 : ℝ)|^4157 ≤ (39841120224797/100000000000000 : ℝ)^3133
        have hw : |(4997841371/10000000000 : ℝ)|=(4997841371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_2 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420280263/10000000000 : ℝ)*x 0 + (1249459993/2500000000 : ℝ)*x 1 + (-62196341/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420280263/10000000000 : ℝ)^4157 ≤ (44369908859773/100000000000000 : ℝ)^3133 := by
    have hnat : (5420280263 : ℕ)^4157*100000000000000^3133 ≤ 44369908859773^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420280263 10000000000 44369908859773 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249459993/2500000000 : ℝ)^4157 ≤ (9960276356841/25000000000000 : ℝ)^3133 := by
    have hnat : (1249459993 : ℕ)^4157*25000000000000^3133 ≤ 9960276356841^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249459993 2500000000 9960276356841 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62196341/250000000 : ℝ)^4157 ≤ (15788985701359/100000000000000 : ℝ)^3133 := by
    have hnat : (62196341 : ℕ)^4157*100000000000000^3133 ≤ 15788985701359^3133*250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62196341 250000000 15788985701359 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420280263/10000000000 : ℝ), (1249459993/2500000000 : ℝ), (-62196341/250000000 : ℝ)] ![(44369908859773/100000000000000 : ℝ), (9960276356841/25000000000000 : ℝ), (15788985701359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420280263/10000000000 : ℝ)|^4157 ≤ (44369908859773/100000000000000 : ℝ)^3133
        have hw : |(5420280263/10000000000 : ℝ)|=(5420280263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249459993/2500000000 : ℝ)|^4157 ≤ (9960276356841/25000000000000 : ℝ)^3133
        have hw : |(1249459993/2500000000 : ℝ)|=(1249459993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62196341/250000000 : ℝ)|^4157 ≤ (15788985701359/100000000000000 : ℝ)^3133
        have hw : |(-62196341/250000000 : ℝ)|=(62196341/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_3 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319210867/10000000000 : ℝ)*x 0 + (3673073377/10000000000 : ℝ)*x 1 + (2539217593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319210867/10000000000 : ℝ)^4157 ≤ (32827573868441/100000000000000 : ℝ)^3133 := by
    have hnat : (4319210867 : ℕ)^4157*100000000000000^3133 ≤ 32827573868441^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319210867 10000000000 32827573868441 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3673073377/10000000000 : ℝ)^4157 ≤ (2647661455161/10000000000000 : ℝ)^3133 := by
    have hnat : (3673073377 : ℕ)^4157*10000000000000^3133 ≤ 2647661455161^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3673073377 10000000000 2647661455161 10000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539217593/5000000000 : ℝ)^4157 ≤ (40695811561583/100000000000000 : ℝ)^3133 := by
    have hnat : (2539217593 : ℕ)^4157*100000000000000^3133 ≤ 40695811561583^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539217593 5000000000 40695811561583 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319210867/10000000000 : ℝ), (3673073377/10000000000 : ℝ), (2539217593/5000000000 : ℝ)] ![(32827573868441/100000000000000 : ℝ), (2647661455161/10000000000000 : ℝ), (40695811561583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319210867/10000000000 : ℝ)|^4157 ≤ (32827573868441/100000000000000 : ℝ)^3133
        have hw : |(4319210867/10000000000 : ℝ)|=(4319210867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3673073377/10000000000 : ℝ)|^4157 ≤ (2647661455161/10000000000000 : ℝ)^3133
        have hw : |(3673073377/10000000000 : ℝ)|=(3673073377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539217593/5000000000 : ℝ)|^4157 ≤ (40695811561583/100000000000000 : ℝ)^3133
        have hw : |(2539217593/5000000000 : ℝ)|=(2539217593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_4 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210548917/1000000000 : ℝ)*x 0 + (1251901201/2500000000 : ℝ)*x 1 + (356075229/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210548917/1000000000 : ℝ)^4157 ≤ (6326528872933/50000000000000 : ℝ)^3133 := by
    have hnat : (210548917 : ℕ)^4157*50000000000000^3133 ≤ 6326528872933^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210548917 1000000000 6326528872933 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251901201/2500000000 : ℝ)^4157 ≤ (624131601309/1562500000000 : ℝ)^3133 := by
    have hnat : (1251901201 : ℕ)^4157*1562500000000^3133 ≤ 624131601309^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251901201 2500000000 624131601309 1562500000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356075229/625000000 : ℝ)^4157 ≤ (23701259878531/50000000000000 : ℝ)^3133 := by
    have hnat : (356075229 : ℕ)^4157*50000000000000^3133 ≤ 23701259878531^3133*625000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356075229 625000000 23701259878531 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210548917/1000000000 : ℝ), (1251901201/2500000000 : ℝ), (356075229/625000000 : ℝ)] ![(6326528872933/50000000000000 : ℝ), (624131601309/1562500000000 : ℝ), (23701259878531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210548917/1000000000 : ℝ)|^4157 ≤ (6326528872933/50000000000000 : ℝ)^3133
        have hw : |(-210548917/1000000000 : ℝ)|=(210548917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251901201/2500000000 : ℝ)|^4157 ≤ (624131601309/1562500000000 : ℝ)^3133
        have hw : |(1251901201/2500000000 : ℝ)|=(1251901201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356075229/625000000 : ℝ)|^4157 ≤ (23701259878531/50000000000000 : ℝ)^3133
        have hw : |(356075229/625000000 : ℝ)|=(356075229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_5 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2619307097/5000000000 : ℝ)*x 0 + (-89424559/500000000 : ℝ)*x 1 + (5697203437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619307097/5000000000 : ℝ)^4157 ≤ (42407648076299/100000000000000 : ℝ)^3133 := by
    have hnat : (2619307097 : ℕ)^4157*100000000000000^3133 ≤ 42407648076299^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619307097 5000000000 42407648076299 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89424559/500000000 : ℝ)^4157 ≤ (5094917323111/50000000000000 : ℝ)^3133 := by
    have hnat : (89424559 : ℕ)^4157*50000000000000^3133 ≤ 5094917323111^3133*500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89424559 500000000 5094917323111 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5697203437/10000000000 : ℝ)^4157 ≤ (23701258625519/50000000000000 : ℝ)^3133 := by
    have hnat : (5697203437 : ℕ)^4157*50000000000000^3133 ≤ 23701258625519^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697203437 10000000000 23701258625519 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619307097/5000000000 : ℝ), (-89424559/500000000 : ℝ), (5697203437/10000000000 : ℝ)] ![(42407648076299/100000000000000 : ℝ), (5094917323111/50000000000000 : ℝ), (23701258625519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619307097/5000000000 : ℝ)|^4157 ≤ (42407648076299/100000000000000 : ℝ)^3133
        have hw : |(2619307097/5000000000 : ℝ)|=(2619307097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89424559/500000000 : ℝ)|^4157 ≤ (5094917323111/50000000000000 : ℝ)^3133
        have hw : |(-89424559/500000000 : ℝ)|=(89424559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5697203437/10000000000 : ℝ)|^4157 ≤ (23701258625519/50000000000000 : ℝ)^3133
        have hw : |(5697203437/10000000000 : ℝ)|=(5697203437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_6 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523861423/1000000000 : ℝ)*x 0 + (2848601797/5000000000 : ℝ)*x 1 + (-1788490901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523861423/1000000000 : ℝ)^4157 ≤ (42407648462977/100000000000000 : ℝ)^3133 := by
    have hnat : (523861423 : ℕ)^4157*100000000000000^3133 ≤ 42407648462977^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523861423 1000000000 42407648462977 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848601797/5000000000 : ℝ)^4157 ≤ (47402518984279/100000000000000 : ℝ)^3133 := by
    have hnat : (2848601797 : ℕ)^4157*100000000000000^3133 ≤ 47402518984279^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848601797 5000000000 47402518984279 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1788490901/10000000000 : ℝ)^4157 ≤ (9951008337/97656250000 : ℝ)^3133 := by
    have hnat : (1788490901 : ℕ)^4157*97656250000^3133 ≤ 9951008337^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788490901 10000000000 9951008337 97656250000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523861423/1000000000 : ℝ), (2848601797/5000000000 : ℝ), (-1788490901/10000000000 : ℝ)] ![(42407648462977/100000000000000 : ℝ), (47402518984279/100000000000000 : ℝ), (9951008337/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523861423/1000000000 : ℝ)|^4157 ≤ (42407648462977/100000000000000 : ℝ)^3133
        have hw : |(523861423/1000000000 : ℝ)|=(523861423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848601797/5000000000 : ℝ)|^4157 ≤ (47402518984279/100000000000000 : ℝ)^3133
        have hw : |(2848601797/5000000000 : ℝ)|=(2848601797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1788490901/10000000000 : ℝ)|^4157 ≤ (9951008337/97656250000 : ℝ)^3133
        have hw : |(-1788490901/10000000000 : ℝ)|=(1788490901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s1_7 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320864909/10000000000 : ℝ)*x 0 + (632386537/1250000000 : ℝ)*x 1 + (3692802027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320864909/10000000000 : ℝ)^4157 ≤ (4105531885617/12500000000000 : ℝ)^3133 := by
    have hnat : (4320864909 : ℕ)^4157*12500000000000^3133 ≤ 4105531885617^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320864909 10000000000 4105531885617 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (632386537/1250000000 : ℝ)^4157 ≤ (40490274496379/100000000000000 : ℝ)^3133 := by
    have hnat : (632386537 : ℕ)^4157*100000000000000^3133 ≤ 40490274496379^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632386537 1250000000 40490274496379 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3692802027/10000000000 : ℝ)^4157 ≤ (3333183799487/12500000000000 : ℝ)^3133 := by
    have hnat : (3692802027 : ℕ)^4157*12500000000000^3133 ≤ 3333183799487^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692802027 10000000000 3333183799487 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320864909/10000000000 : ℝ), (632386537/1250000000 : ℝ), (3692802027/10000000000 : ℝ)] ![(4105531885617/12500000000000 : ℝ), (40490274496379/100000000000000 : ℝ), (3333183799487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320864909/10000000000 : ℝ)|^4157 ≤ (4105531885617/12500000000000 : ℝ)^3133
        have hw : |(4320864909/10000000000 : ℝ)|=(4320864909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(632386537/1250000000 : ℝ)|^4157 ≤ (40490274496379/100000000000000 : ℝ)^3133
        have hw : |(632386537/1250000000 : ℝ)|=(632386537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3692802027/10000000000 : ℝ)|^4157 ≤ (3333183799487/12500000000000 : ℝ)^3133
        have hw : |(3692802027/10000000000 : ℝ)|=(3692802027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1121_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3487/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5531/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20533/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3487/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (327/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3487/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (327/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3487/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (327/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3487/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (327/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3487/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (327/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3487/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (327/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (327/100000 : ℝ) ^ (8313/2048 : ℝ) ≤ (8153525679/100000000000000000000 : ℝ) := by
    have hpowers : (327/100000 : ℝ)^8313 ≤ (8153525679/100000000000000000000 : ℝ)^2048 := by
      have hnat : (327 : ℕ)^8313*100000000000000000000^2048 ≤ 8153525679^2048*100000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 100000 8153525679 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/100000 : ℝ)) (X := (8153525679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3487/12500 : ℝ) ^ (8313/2048 : ℝ) ≤ (561576891679474969/100000000000000000000 : ℝ) := by
    have hpowers : (3487/12500 : ℝ)^8313 ≤ (561576891679474969/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3487 : ℕ)^8313*100000000000000000000^2048 ≤ 561576891679474969^2048*12500^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3487 12500 561576891679474969 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3487/12500 : ℝ)) (X := (561576891679474969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000008153525679/50000000000000000000 : ℝ) ≤ (10000000000401743/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (50000000008153525679/50000000000000000000 : ℝ)^2048 ≤ (10000000000401743/10000000000000000 : ℝ)^8313 := by
      have hnat : (50000000008153525679 : ℕ)^2048*10000000000000000^8313 ≤ 10000000000401743^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000008153525679 50000000000000000000 10000000000401743 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000401743/10000000000000000 : ℝ)) (X := (50000000008153525679/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12570197112479125081/12500000000000000000 : ℝ) ≤ (10013805890378449/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (12570197112479125081/12500000000000000000 : ℝ)^2048 ≤ (10013805890378449/10000000000000000 : ℝ)^8313 := by
      have hnat : (12570197112479125081 : ℕ)^2048*10000000000000000^8313 ≤ 10013805890378449^8313*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12570197112479125081 12500000000000000000 10013805890378449 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013805890378449/10000000000000000 : ℝ)) (X := (12570197112479125081/12500000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50561576891679474969/50000000000000000000 : ℝ) ≤ (2005522356071031/2000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (50561576891679474969/50000000000000000000 : ℝ)^2048 ≤ (2005522356071031/2000000000000000 : ℝ)^8313 := by
      have hnat : (50561576891679474969 : ℕ)^2048*2000000000000000^8313 ≤ 2005522356071031^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50561576891679474969 50000000000000000000 2005522356071031 2000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005522356071031/2000000000000000 : ℝ)) (X := (50561576891679474969/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8153525679/100000000000000000000 : ℝ) ≤ ((275680970959030887043/275690000000000000000 : ℝ)+2*(6902944988353/1378450000000000 : ℝ)*(327/100000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (275680970959030887043/275690000000000000000 : ℝ)+2*(6902944988353/1378450000000000 : ℝ)*(327/100000 : ℝ)=(10000000000401743/10000000000000000 : ℝ) by norm_num, show 1+2*(8153525679/100000000000000000000 : ℝ)=(50000000008153525679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(561576891679474969/100000000000000000000 : ℝ)+(8153525679/100000000000000000000 : ℝ) ≤ ((275680970959030887043/275690000000000000000 : ℝ)+(6902944988353/1378450000000000 : ℝ)*((3487/12500 : ℝ)+(327/100000 : ℝ)))^(8313/2048 : ℝ) := by
    rw [show (275680970959030887043/275690000000000000000 : ℝ)+(6902944988353/1378450000000000 : ℝ)*((3487/12500 : ℝ)+(327/100000 : ℝ))=(10013805890378449/10000000000000000 : ℝ) by norm_num, show 1+(561576891679474969/100000000000000000000 : ℝ)+(8153525679/100000000000000000000 : ℝ)=(12570197112479125081/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(561576891679474969/100000000000000000000 : ℝ) ≤ ((275680970959030887043/275690000000000000000 : ℝ)+2*(6902944988353/1378450000000000 : ℝ)*(3487/12500 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (275680970959030887043/275690000000000000000 : ℝ)+2*(6902944988353/1378450000000000 : ℝ)*(3487/12500 : ℝ)=(2005522356071031/2000000000000000 : ℝ) by norm_num, show 1+2*(561576891679474969/100000000000000000000 : ℝ)=(50561576891679474969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (275680970959030887043/275690000000000000000 : ℝ)*(X 1 0+X 2 0)+(6902944988353/1378450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (327/100000 : ℝ)) (hi := (3487/12500 : ℝ)) (c := (275680970959030887043/275690000000000000000 : ℝ)) (alpha := (6902944988353/1378450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (275680970959030887043/275690000000000000000 : ℝ)*(X 0 1+X 2 1)+(6902944988353/1378450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (327/100000 : ℝ)) (hi := (3487/12500 : ℝ)) (c := (275680970959030887043/275690000000000000000 : ℝ)) (alpha := (6902944988353/1378450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (275680970959030887043/275690000000000000000 : ℝ)*(X 0 2+X 1 2)+(6902944988353/1378450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (327/100000 : ℝ)) (hi := (3487/12500 : ℝ)) (c := (275680970959030887043/275690000000000000000 : ℝ)) (alpha := (6902944988353/1378450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1052326593/5000000000 : ℝ)*X 0 0+(1426790417/2500000000 : ℝ)*X 0 1+(1249460401/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420278737/10000000000 : ℝ)*X 1 0+(-49757077/200000000 : ℝ)*X 1 1+(4997841371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420280263/10000000000 : ℝ)*X 2 0+(1249459993/2500000000 : ℝ)*X 2 1+(-62196341/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319210867/10000000000 : ℝ)*X 0 0+(3673073377/10000000000 : ℝ)*X 0 1+(2539217593/5000000000 : ℝ)*X 0 2+(4319210867/10000000000 : ℝ)*X 1 0+(3673073377/10000000000 : ℝ)*X 1 1+(2539217593/5000000000 : ℝ)*X 1 2+(4319210867/10000000000 : ℝ)*X 2 0+(3673073377/10000000000 : ℝ)*X 2 1+(2539217593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210548917/1000000000 : ℝ)*X 0 0+(1251901201/2500000000 : ℝ)*X 0 1+(356075229/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619307097/5000000000 : ℝ)*X 1 0+(-89424559/500000000 : ℝ)*X 1 1+(5697203437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((523861423/1000000000 : ℝ)*X 2 0+(2848601797/5000000000 : ℝ)*X 2 1+(-1788490901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320864909/10000000000 : ℝ)*X 0 0+(632386537/1250000000 : ℝ)*X 0 1+(3692802027/10000000000 : ℝ)*X 0 2+(4320864909/10000000000 : ℝ)*X 1 0+(632386537/1250000000 : ℝ)*X 1 1+(3692802027/10000000000 : ℝ)*X 1 2+(4320864909/10000000000 : ℝ)*X 2 0+(632386537/1250000000 : ℝ)*X 2 1+(3692802027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8898173691352766223363543243/1378450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82517139/25000000000000 : ℝ)*(base1) + (34665971/3125000000000 : ℝ)*(base19) + (18827767/1250000000000 : ℝ)*(base23) + (8585123/100000000000000 : ℝ)*(upper3) + (188409173/100000000000000 : ℝ)*(upper5) + (106068562874467/10000000000000 : ℝ)*(major0) + (106068562874467/10000000000000 : ℝ)*(major1) + (106068562874467/10000000000000 : ℝ)*(major2) + (1409803136741633/100000000000000 : ℝ)*(sp0) + (1409806680450657/100000000000000 : ℝ)*(sp1) + (1409806283540369/100000000000000 : ℝ)*(sp2) + (355780948690149/50000000000000 : ℝ)*(sp3) + (1245772163/25000000000000 : ℝ)*(sp4) + (512552669/50000000000000 : ℝ)*(sp7) + (44472703284637/6250000000000 : ℝ)*(f.failure) + (1409807789761729/100000000000000 : ℝ)*(f.sum) + (50188266737333/13784500000000000000000000000 : ℝ)*base66 + (10001542922858631081/2756900000000000000000000000000000 : ℝ)*base67 + (11766926707180568919/2756900000000000000000000000000000 : ℝ)*base70 + (1849963178751268919/2756900000000000000000000000000000 : ℝ)*base72 + (847417827933/6892250000000000000000000000 : ℝ)*base74 + (11384297898790868919/2756900000000000000000000000000000 : ℝ)*base76 + (14306416884566531081/2756900000000000000000000000000000 : ℝ)*base77 + (15012973130291768919/2756900000000000000000000000000000 : ℝ)*base80 + (106426288639391/13784500000000000000000000000 : ℝ)*base82 + (2226047/312500000000000000000 : ℝ)*base90 + (2226047/312500000000000000000 : ℝ)*base92 + (2226047/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15993916227994987741997749047/3446125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58447659/100000000000000 : ℝ)*(base1) + (1045744171/100000000000000 : ℝ)*(base19) + (1074958207/100000000000000 : ℝ)*(base23) + (48892743/50000000000000 : ℝ)*(upper3) + (102480863/100000000000000 : ℝ)*(upper5) + (272753448739543/25000000000000 : ℝ)*(major0) + (272753448739543/25000000000000 : ℝ)*(major1) + (272753448739543/25000000000000 : ℝ)*(major2) + (4088875559/100000000000000 : ℝ)*(sp1) + (4643909129/100000000000000 : ℝ)*(sp2) + (290023705015969/20000000000000 : ℝ)*(sp4) + (181264166501557/12500000000000 : ℝ)*(sp5) + (29002254955297/2000000000000 : ℝ)*(sp6) + (731908910132143/100000000000000 : ℝ)*(sp7) + (365954484289901/50000000000000 : ℝ)*(f.failure) + (725059233316093/50000000000000 : ℝ)*(f.sum) + (163181302007333/137845000000000000000000000000 : ℝ)*base66 + (21993406731133241349/6892250000000000000000000000000000 : ℝ)*base67 + (21818973984761008651/6892250000000000000000000000000000 : ℝ)*base70 + (1581913753109741349/6892250000000000000000000000000000 : ℝ)*base71 + (197601386616311/68922500000000000000000000000 : ℝ)*base73 + (2964607811658258651/6892250000000000000000000000000000 : ℝ)*base76 + (10237929569795258651/6892250000000000000000000000000000 : ℝ)*base78 + (4425965334779758651/6892250000000000000000000000000000 : ℝ)*base80 + (380266929506663/137845000000000000000000000000 : ℝ)*base82 + (17335169/2500000000000000000000 : ℝ)*base89 + (17335169/2500000000000000000000 : ℝ)*base91 + (17335169/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1121_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3487/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5531/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20533/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1121_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1121_s2_0 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107951279/500000000 : ℝ)*x 0 + (2757426119/5000000000 : ℝ)*x 1 + (5155597813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107951279/500000000 : ℝ)^4157 ≤ (1308170703303/10000000000000 : ℝ)^3133 := by
    have hnat : (107951279 : ℕ)^4157*10000000000000^3133 ≤ 1308170703303^3133*500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107951279 500000000 1308170703303 10000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757426119/5000000000 : ℝ)^4157 ≤ (22700005922189/50000000000000 : ℝ)^3133 := by
    have hnat : (2757426119 : ℕ)^4157*50000000000000^3133 ≤ 22700005922189^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757426119 5000000000 22700005922189 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155597813/10000000000 : ℝ)^4157 ≤ (41518281116623/100000000000000 : ℝ)^3133 := by
    have hnat : (5155597813 : ℕ)^4157*100000000000000^3133 ≤ 41518281116623^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155597813 10000000000 41518281116623 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107951279/500000000 : ℝ), (2757426119/5000000000 : ℝ), (5155597813/10000000000 : ℝ)] ![(1308170703303/10000000000000 : ℝ), (22700005922189/50000000000000 : ℝ), (41518281116623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107951279/500000000 : ℝ)|^4157 ≤ (1308170703303/10000000000000 : ℝ)^3133
        have hw : |(-107951279/500000000 : ℝ)|=(107951279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757426119/5000000000 : ℝ)|^4157 ≤ (22700005922189/50000000000000 : ℝ)^3133
        have hw : |(2757426119/5000000000 : ℝ)|=(2757426119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155597813/10000000000 : ℝ)|^4157 ≤ (41518281116623/100000000000000 : ℝ)^3133
        have hw : |(5155597813/10000000000 : ℝ)|=(5155597813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_1 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335923243/625000000 : ℝ)*x 0 + (-586489321/2500000000 : ℝ)*x 1 + (5155599301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335923243/625000000 : ℝ)^4157 ≤ (21938151488027/50000000000000 : ℝ)^3133 := by
    have hnat : (335923243 : ℕ)^4157*50000000000000^3133 ≤ 21938151488027^3133*625000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335923243 625000000 21938151488027 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586489321/2500000000 : ℝ)^4157 ≤ (14605399997169/100000000000000 : ℝ)^3133 := by
    have hnat : (586489321 : ℕ)^4157*100000000000000^3133 ≤ 14605399997169^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586489321 2500000000 14605399997169 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155599301/10000000000 : ℝ)^4157 ≤ (20759148508051/50000000000000 : ℝ)^3133 := by
    have hnat : (5155599301 : ℕ)^4157*50000000000000^3133 ≤ 20759148508051^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155599301 10000000000 20759148508051 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335923243/625000000 : ℝ), (-586489321/2500000000 : ℝ), (5155599301/10000000000 : ℝ)] ![(21938151488027/50000000000000 : ℝ), (14605399997169/100000000000000 : ℝ), (20759148508051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335923243/625000000 : ℝ)|^4157 ≤ (21938151488027/50000000000000 : ℝ)^3133
        have hw : |(335923243/625000000 : ℝ)|=(335923243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-586489321/2500000000 : ℝ)|^4157 ≤ (14605399997169/100000000000000 : ℝ)^3133
        have hw : |(-586489321/2500000000 : ℝ)|=(586489321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155599301/10000000000 : ℝ)|^4157 ≤ (20759148508051/50000000000000 : ℝ)^3133
        have hw : |(5155599301/10000000000 : ℝ)|=(5155599301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_2 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343692953/2500000000 : ℝ)*x 0 + (2577799677/5000000000 : ℝ)*x 1 + (-1172978657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343692953/2500000000 : ℝ)^4157 ≤ (21938151076429/50000000000000 : ℝ)^3133 := by
    have hnat : (1343692953 : ℕ)^4157*50000000000000^3133 ≤ 21938151076429^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343692953 2500000000 21938151076429 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577799677/5000000000 : ℝ)^4157 ≤ (20759148791207/50000000000000 : ℝ)^3133 := by
    have hnat : (2577799677 : ℕ)^4157*50000000000000^3133 ≤ 20759148791207^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577799677 5000000000 20759148791207 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1172978657/5000000000 : ℝ)^4157 ≤ (3651350061247/25000000000000 : ℝ)^3133 := by
    have hnat : (1172978657 : ℕ)^4157*25000000000000^3133 ≤ 3651350061247^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172978657 5000000000 3651350061247 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343692953/2500000000 : ℝ), (2577799677/5000000000 : ℝ), (-1172978657/5000000000 : ℝ)] ![(21938151076429/50000000000000 : ℝ), (20759148791207/50000000000000 : ℝ), (3651350061247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343692953/2500000000 : ℝ)|^4157 ≤ (21938151076429/50000000000000 : ℝ)^3133
        have hw : |(1343692953/2500000000 : ℝ)|=(1343692953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577799677/5000000000 : ℝ)|^4157 ≤ (20759148791207/50000000000000 : ℝ)^3133
        have hw : |(2577799677/5000000000 : ℝ)|=(2577799677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1172978657/5000000000 : ℝ)|^4157 ≤ (3651350061247/25000000000000 : ℝ)^3133
        have hw : |(-1172978657/5000000000 : ℝ)|=(1172978657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_3 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871291293/2000000000 : ℝ)*x 0 + (401504179/1000000000 : ℝ)*x 1 + (189072911/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871291293/2000000000 : ℝ)^4157 ≤ (33203705077881/100000000000000 : ℝ)^3133 := by
    have hnat : (871291293 : ℕ)^4157*100000000000000^3133 ≤ 33203705077881^3133*2000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871291293 2000000000 33203705077881 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401504179/1000000000 : ℝ)^4157 ≤ (3724507430351/12500000000000 : ℝ)^3133 := by
    have hnat : (401504179 : ℕ)^4157*12500000000000^3133 ≤ 3724507430351^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401504179 1000000000 3724507430351 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189072911/400000000 : ℝ)^4157 ≤ (2312514716969/6250000000000 : ℝ)^3133 := by
    have hnat : (189072911 : ℕ)^4157*6250000000000^3133 ≤ 2312514716969^3133*400000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189072911 400000000 2312514716969 6250000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871291293/2000000000 : ℝ), (401504179/1000000000 : ℝ), (189072911/400000000 : ℝ)] ![(33203705077881/100000000000000 : ℝ), (3724507430351/12500000000000 : ℝ), (2312514716969/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871291293/2000000000 : ℝ)|^4157 ≤ (33203705077881/100000000000000 : ℝ)^3133
        have hw : |(871291293/2000000000 : ℝ)|=(871291293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401504179/1000000000 : ℝ)|^4157 ≤ (3724507430351/12500000000000 : ℝ)^3133
        have hw : |(401504179/1000000000 : ℝ)|=(401504179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(189072911/400000000 : ℝ)|^4157 ≤ (2312514716969/6250000000000 : ℝ)^3133
        have hw : |(189072911/400000000 : ℝ)|=(189072911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_4 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079567087/5000000000 : ℝ)*x 0 + (5158111947/10000000000 : ℝ)*x 1 + (5512312537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079567087/5000000000 : ℝ)^4157 ≤ (6541290038041/50000000000000 : ℝ)^3133 := by
    have hnat : (1079567087 : ℕ)^4157*50000000000000^3133 ≤ 6541290038041^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079567087 5000000000 6541290038041 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158111947/10000000000 : ℝ)^4157 ≤ (20772573557687/50000000000000 : ℝ)^3133 := by
    have hnat : (5158111947 : ℕ)^4157*50000000000000^3133 ≤ 20772573557687^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158111947 10000000000 20772573557687 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5512312537/10000000000 : ℝ)^4157 ≤ (453722727923/1000000000000 : ℝ)^3133 := by
    have hnat : (5512312537 : ℕ)^4157*1000000000000^3133 ≤ 453722727923^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512312537 10000000000 453722727923 1000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079567087/5000000000 : ℝ), (5158111947/10000000000 : ℝ), (5512312537/10000000000 : ℝ)] ![(6541290038041/50000000000000 : ℝ), (20772573557687/50000000000000 : ℝ), (453722727923/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079567087/5000000000 : ℝ)|^4157 ≤ (6541290038041/50000000000000 : ℝ)^3133
        have hw : |(-1079567087/5000000000 : ℝ)|=(1079567087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158111947/10000000000 : ℝ)|^4157 ≤ (20772573557687/50000000000000 : ℝ)^3133
        have hw : |(5158111947/10000000000 : ℝ)|=(5158111947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5512312537/10000000000 : ℝ)|^4157 ≤ (453722727923/1000000000000 : ℝ)^3133
        have hw : |(5512312537/10000000000 : ℝ)|=(5512312537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_5 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660468513/1250000000 : ℝ)*x 0 + (-497310613/2500000000 : ℝ)*x 1 + (2756156523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660468513/1250000000 : ℝ)^4157 ≤ (8578623130941/20000000000000 : ℝ)^3133 := by
    have hnat : (660468513 : ℕ)^4157*20000000000000^3133 ≤ 8578623130941^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660468513 1250000000 8578623130941 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497310613/2500000000 : ℝ)^4157 ≤ (2346921196633/20000000000000 : ℝ)^3133 := by
    have hnat : (497310613 : ℕ)^4157*20000000000000^3133 ≤ 2346921196633^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497310613 2500000000 2346921196633 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756156523/5000000000 : ℝ)^4157 ≤ (11343069587817/25000000000000 : ℝ)^3133 := by
    have hnat : (2756156523 : ℕ)^4157*25000000000000^3133 ≤ 11343069587817^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756156523 5000000000 11343069587817 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660468513/1250000000 : ℝ), (-497310613/2500000000 : ℝ), (2756156523/5000000000 : ℝ)] ![(8578623130941/20000000000000 : ℝ), (2346921196633/20000000000000 : ℝ), (11343069587817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660468513/1250000000 : ℝ)|^4157 ≤ (8578623130941/20000000000000 : ℝ)^3133
        have hw : |(660468513/1250000000 : ℝ)|=(660468513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497310613/2500000000 : ℝ)|^4157 ≤ (2346921196633/20000000000000 : ℝ)^3133
        have hw : |(-497310613/2500000000 : ℝ)|=(497310613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756156523/5000000000 : ℝ)|^4157 ≤ (11343069587817/25000000000000 : ℝ)^3133
        have hw : |(2756156523/5000000000 : ℝ)|=(2756156523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_6 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66046837/125000000 : ℝ)*x 0 + (110246259/200000000 : ℝ)*x 1 + (-1989244159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66046837/125000000 : ℝ)^4157 ≤ (5361637916553/12500000000000 : ℝ)^3133 := by
    have hnat : (66046837 : ℕ)^4157*12500000000000^3133 ≤ 5361637916553^3133*125000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66046837 125000000 5361637916553 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110246259/200000000 : ℝ)^4157 ≤ (22686138651409/50000000000000 : ℝ)^3133 := by
    have hnat : (110246259 : ℕ)^4157*50000000000000^3133 ≤ 22686138651409^3133*200000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110246259 200000000 22686138651409 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989244159/10000000000 : ℝ)^4157 ≤ (2933654836003/25000000000000 : ℝ)^3133 := by
    have hnat : (1989244159 : ℕ)^4157*25000000000000^3133 ≤ 2933654836003^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989244159 10000000000 2933654836003 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66046837/125000000 : ℝ), (110246259/200000000 : ℝ), (-1989244159/10000000000 : ℝ)] ![(5361637916553/12500000000000 : ℝ), (22686138651409/50000000000000 : ℝ), (2933654836003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66046837/125000000 : ℝ)|^4157 ≤ (5361637916553/12500000000000 : ℝ)^3133
        have hw : |(66046837/125000000 : ℝ)|=(66046837/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110246259/200000000 : ℝ)|^4157 ≤ (22686138651409/50000000000000 : ℝ)^3133
        have hw : |(110246259/200000000 : ℝ)|=(110246259/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989244159/10000000000 : ℝ)|^4157 ≤ (2933654836003/25000000000000 : ℝ)^3133
        have hw : |(-1989244159/10000000000 : ℝ)|=(1989244159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s2_7 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356671277/10000000000 : ℝ)*x 0 + (188873707/400000000 : ℝ)*x 1 + (4020072199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356671277/10000000000 : ℝ)^4157 ≤ (6641175490617/20000000000000 : ℝ)^3133 := by
    have hnat : (4356671277 : ℕ)^4157*20000000000000^3133 ≤ 6641175490617^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356671277 10000000000 6641175490617 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188873707/400000000 : ℝ)^4157 ≤ (9237130072257/25000000000000 : ℝ)^3133 := by
    have hnat : (188873707 : ℕ)^4157*25000000000000^3133 ≤ 9237130072257^3133*400000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188873707 400000000 9237130072257 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020072199/10000000000 : ℝ)^4157 ≤ (14922801123021/50000000000000 : ℝ)^3133 := by
    have hnat : (4020072199 : ℕ)^4157*50000000000000^3133 ≤ 14922801123021^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020072199 10000000000 14922801123021 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356671277/10000000000 : ℝ), (188873707/400000000 : ℝ), (4020072199/10000000000 : ℝ)] ![(6641175490617/20000000000000 : ℝ), (9237130072257/25000000000000 : ℝ), (14922801123021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356671277/10000000000 : ℝ)|^4157 ≤ (6641175490617/20000000000000 : ℝ)^3133
        have hw : |(4356671277/10000000000 : ℝ)|=(4356671277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188873707/400000000 : ℝ)|^4157 ≤ (9237130072257/25000000000000 : ℝ)^3133
        have hw : |(188873707/400000000 : ℝ)|=(188873707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020072199/10000000000 : ℝ)|^4157 ≤ (14922801123021/50000000000000 : ℝ)^3133
        have hw : |(4020072199/10000000000 : ℝ)|=(4020072199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1121_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5531/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4487/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8283/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5531/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5531/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5531/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5531/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5531/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5531/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5531/100000 : ℝ) ^ (8313/2048 : ℝ) ≤ (157749109387207/20000000000000000000 : ℝ) := by
    have hpowers : (5531/100000 : ℝ)^8313 ≤ (157749109387207/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5531 : ℕ)^8313*20000000000000000000^2048 ≤ 157749109387207^2048*100000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5531 100000 157749109387207 20000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5531/100000 : ℝ)) (X := (157749109387207/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20533/100000 : ℝ) ^ (8313/2048 : ℝ) ≤ (32375606723574049/20000000000000000000 : ℝ) := by
    have hpowers : (20533/100000 : ℝ)^8313 ≤ (32375606723574049/20000000000000000000 : ℝ)^2048 := by
      have hnat : (20533 : ℕ)^8313*20000000000000000000^2048 ≤ 32375606723574049^2048*100000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20533 100000 32375606723574049 20000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20533/100000 : ℝ)) (X := (32375606723574049/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000157749109387207/10000000000000000000 : ℝ) ≤ (2000007772603287/2000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (10000157749109387207/10000000000000000000 : ℝ)^2048 ≤ (2000007772603287/2000000000000000 : ℝ)^8313 := by
      have hnat : (10000157749109387207 : ℕ)^2048*2000000000000000^8313 ≤ 2000007772603287^8313*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000157749109387207 10000000000000000000 2000007772603287 2000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000007772603287/2000000000000000 : ℝ)) (X := (10000157749109387207/10000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2504066669479120157/2500000000000000000 : ℝ) ≤ (400160200916739/400000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (2504066669479120157/2500000000000000000 : ℝ)^2048 ≤ (400160200916739/400000000000000 : ℝ)^8313 := by
      have hnat : (2504066669479120157 : ℕ)^2048*400000000000000^8313 ≤ 400160200916739^8313*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2504066669479120157 2500000000000000000 400160200916739 400000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400160200916739/400000000000000 : ℝ)) (X := (2504066669479120157/2500000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10032375606723574049/10000000000000000000 : ℝ) ≤ (2001594236564103/2000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (10032375606723574049/10000000000000000000 : ℝ)^2048 ≤ (2001594236564103/2000000000000000 : ℝ)^8313 := by
      have hnat : (10032375606723574049 : ℕ)^2048*2000000000000000^8313 ≤ 2001594236564103^8313*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10032375606723574049 10000000000000000000 2001594236564103 2000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001594236564103/2000000000000000 : ℝ)) (X := (10032375606723574049/10000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(157749109387207/20000000000000000000 : ℝ) ≤ ((14997670936213619139/15002000000000000000 : ℝ)+2*(99153997551/37505000000000 : ℝ)*(5531/100000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (14997670936213619139/15002000000000000000 : ℝ)+2*(99153997551/37505000000000 : ℝ)*(5531/100000 : ℝ)=(2000007772603287/2000000000000000 : ℝ) by norm_num, show 1+2*(157749109387207/20000000000000000000 : ℝ)=(10000157749109387207/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32375606723574049/20000000000000000000 : ℝ)+(157749109387207/20000000000000000000 : ℝ) ≤ ((14997670936213619139/15002000000000000000 : ℝ)+(99153997551/37505000000000 : ℝ)*((20533/100000 : ℝ)+(5531/100000 : ℝ)))^(8313/2048 : ℝ) := by
    rw [show (14997670936213619139/15002000000000000000 : ℝ)+(99153997551/37505000000000 : ℝ)*((20533/100000 : ℝ)+(5531/100000 : ℝ))=(400160200916739/400000000000000 : ℝ) by norm_num, show 1+(32375606723574049/20000000000000000000 : ℝ)+(157749109387207/20000000000000000000 : ℝ)=(2504066669479120157/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32375606723574049/20000000000000000000 : ℝ) ≤ ((14997670936213619139/15002000000000000000 : ℝ)+2*(99153997551/37505000000000 : ℝ)*(20533/100000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (14997670936213619139/15002000000000000000 : ℝ)+2*(99153997551/37505000000000 : ℝ)*(20533/100000 : ℝ)=(2001594236564103/2000000000000000 : ℝ) by norm_num, show 1+2*(32375606723574049/20000000000000000000 : ℝ)=(10032375606723574049/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14997670936213619139/15002000000000000000 : ℝ)*(X 1 0+X 2 0)+(99153997551/37505000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (5531/100000 : ℝ)) (hi := (20533/100000 : ℝ)) (c := (14997670936213619139/15002000000000000000 : ℝ)) (alpha := (99153997551/37505000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14997670936213619139/15002000000000000000 : ℝ)*(X 0 1+X 2 1)+(99153997551/37505000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (5531/100000 : ℝ)) (hi := (20533/100000 : ℝ)) (c := (14997670936213619139/15002000000000000000 : ℝ)) (alpha := (99153997551/37505000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14997670936213619139/15002000000000000000 : ℝ)*(X 0 2+X 1 2)+(99153997551/37505000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (5531/100000 : ℝ)) (hi := (20533/100000 : ℝ)) (c := (14997670936213619139/15002000000000000000 : ℝ)) (alpha := (99153997551/37505000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107951279/500000000 : ℝ)*X 0 0+(2757426119/5000000000 : ℝ)*X 0 1+(5155597813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335923243/625000000 : ℝ)*X 1 0+(-586489321/2500000000 : ℝ)*X 1 1+(5155599301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343692953/2500000000 : ℝ)*X 2 0+(2577799677/5000000000 : ℝ)*X 2 1+(-1172978657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871291293/2000000000 : ℝ)*X 0 0+(401504179/1000000000 : ℝ)*X 0 1+(189072911/400000000 : ℝ)*X 0 2+(871291293/2000000000 : ℝ)*X 1 0+(401504179/1000000000 : ℝ)*X 1 1+(189072911/400000000 : ℝ)*X 1 2+(871291293/2000000000 : ℝ)*X 2 0+(401504179/1000000000 : ℝ)*X 2 1+(189072911/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079567087/5000000000 : ℝ)*X 0 0+(5158111947/10000000000 : ℝ)*X 0 1+(5512312537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660468513/1250000000 : ℝ)*X 1 0+(-497310613/2500000000 : ℝ)*X 1 1+(2756156523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66046837/125000000 : ℝ)*X 2 0+(110246259/200000000 : ℝ)*X 2 1+(-1989244159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356671277/10000000000 : ℝ)*X 0 0+(188873707/400000000 : ℝ)*X 0 1+(4020072199/10000000000 : ℝ)*X 0 2+(4356671277/10000000000 : ℝ)*X 1 0+(188873707/400000000 : ℝ)*X 1 1+(4020072199/10000000000 : ℝ)*X 1 2+(4356671277/10000000000 : ℝ)*X 2 0+(188873707/400000000 : ℝ)*X 2 1+(4020072199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6250761805897731123663/750100000000000000000000000 : ℝ) := by norm_num
    linear_combination (178314503/20000000000000 : ℝ)*(base19) + (144196971/25000000000000 : ℝ)*(base23) + (9922449/4000000000000 : ℝ)*(upper3) + (29606873/20000000000000 : ℝ)*(upper4) + (9542981/100000000000000 : ℝ)*(upper5) + (209425838076379/10000000000000 : ℝ)*(major0) + (209425838076379/10000000000000 : ℝ)*(major1) + (209425838076379/10000000000000 : ℝ)*(major2) + (1391780972643499/50000000000000 : ℝ)*(sp0) + (1391788909588573/50000000000000 : ℝ)*(sp1) + (173973633372611/6250000000000 : ℝ)*(sp2) + (702465506668639/50000000000000 : ℝ)*(sp3) + (8382731331/50000000000000 : ℝ)*(sp4) + (3379833019/50000000000000 : ℝ)*(sp7) + (351234443250829/25000000000000 : ℝ)*(f.failure) + (139178935537483/5000000000000 : ℝ)*(f.sum) + (5238235602451/937625000000000000000000000 : ℝ)*base66 + (21830526444342319/150020000000000000000000000000000 : ℝ)*base68 + (561541870372217681/150020000000000000000000000000000 : ℝ)*base69 + (1058816883259062319/150020000000000000000000000000000 : ℝ)*base72 + (1073098509823/3750500000000000000000000000 : ℝ)*base74 + (251363414249342319/150020000000000000000000000000000 : ℝ)*base76 + (153736799411657681/150020000000000000000000000000000 : ℝ)*base77 + (54819452290337681/150020000000000000000000000000000 : ℝ)*base79 + (6397017812797/1875250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3664799/1250000000000000000000 : ℝ)*base90 + (3664799/1250000000000000000000 : ℝ)*base92 + (3664799/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1117312223281269011565054141/150020000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267127453/20000000000000 : ℝ)*(base19) + (440747551/50000000000000 : ℝ)*(base23) + (206267949/100000000000000 : ℝ)*(upper2) + (17671659/25000000000000 : ℝ)*(upper3) + (222254337/100000000000000 : ℝ)*(upper5) + (424822029653173/20000000000000 : ℝ)*(major0) + (424822029653173/20000000000000 : ℝ)*(major1) + (424822029653173/20000000000000 : ℝ)*(major2) + (18850108933/100000000000000 : ℝ)*(sp1) + (2655099053/50000000000000 : ℝ)*(sp2) + (1411628076176107/50000000000000 : ℝ)*(sp4) + (564647193321203/20000000000000 : ℝ)*(sp5) + (1411624980329503/50000000000000 : ℝ)*(sp6) + (712481947960503/50000000000000 : ℝ)*(sp7) + (712481947960503/50000000000000 : ℝ)*(f.failure) + (1411628076176107/50000000000000 : ℝ)*(f.sum) + (4553508645983/3750500000000000000000000000 : ℝ)*base66 + (2336562870654241953/300040000000000000000000000000000 : ℝ)*base68 + (676137731350401953/300040000000000000000000000000000 : ℝ)*base70 + (713663566585038047/300040000000000000000000000000000 : ℝ)*base71 + (8413451506419/3750500000000000000000000000 : ℝ)*base74 + (1033093954325398047/300040000000000000000000000000000 : ℝ)*base75 + (2561689719365681953/300040000000000000000000000000000 : ℝ)*base78 + (1444919170476881953/300040000000000000000000000000000 : ℝ)*base80 + (68421094917/14650390625000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6129293/2500000000000000000000 : ℝ)*base90 + (6129293/2500000000000000000000 : ℝ)*base92 + (6129293/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1121_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5531/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8283/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1121_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1121_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8283/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1121_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1121_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1121_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8283/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1121_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
