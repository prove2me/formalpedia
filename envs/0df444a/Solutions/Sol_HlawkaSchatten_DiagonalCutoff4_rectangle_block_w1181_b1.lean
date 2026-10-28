-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:26.166817+00:00
-- url     : https://prove2.me/submissions/b1ea95dd-5d56-4680-9673-cef4f94ff606

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
theorem support_rectangle_w1181_s3_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144978547/10000000000 : ℝ)*x 0 + (2712639849/5000000000 : ℝ)*x 1 + (523561717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144978547/10000000000 : ℝ)^4187 ≤ (13030936416073/100000000000000 : ℝ)^3163 := by
    have hnat : (2144978547 : ℕ)^4187*100000000000000^3163 ≤ 13030936416073^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144978547 10000000000 13030936416073 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712639849/5000000000 : ℝ)^4187 ≤ (44508512765691/100000000000000 : ℝ)^3163 := by
    have hnat : (2712639849 : ℕ)^4187*100000000000000^3163 ≤ 44508512765691^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712639849 5000000000 44508512765691 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523561717/1000000000 : ℝ)^4187 ≤ (4246055080101/10000000000000 : ℝ)^3163 := by
    have hnat : (523561717 : ℕ)^4187*10000000000000^3163 ≤ 4246055080101^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523561717 1000000000 4246055080101 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144978547/10000000000 : ℝ), (2712639849/5000000000 : ℝ), (523561717/1000000000 : ℝ)] ![(13030936416073/100000000000000 : ℝ), (44508512765691/100000000000000 : ℝ), (4246055080101/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144978547/10000000000 : ℝ)|^4187 ≤ (13030936416073/100000000000000 : ℝ)^3163
        have hw : |(-2144978547/10000000000 : ℝ)|=(2144978547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712639849/5000000000 : ℝ)|^4187 ≤ (44508512765691/100000000000000 : ℝ)^3163
        have hw : |(2712639849/5000000000 : ℝ)|=(2712639849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523561717/1000000000 : ℝ)|^4187 ≤ (4246055080101/10000000000000 : ℝ)^3163
        have hw : |(523561717/1000000000 : ℝ)|=(523561717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352871341/10000000000 : ℝ)*x 0 + (-2241847423/10000000000 : ℝ)*x 1 + (2617808487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352871341/10000000000 : ℝ)^4187 ≤ (21861935613853/50000000000000 : ℝ)^3163 := by
    have hnat : (5352871341 : ℕ)^4187*50000000000000^3163 ≤ 21861935613853^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352871341 10000000000 21861935613853 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241847423/10000000000 : ℝ)^4187 ≤ (552623202387/4000000000000 : ℝ)^3163 := by
    have hnat : (2241847423 : ℕ)^4187*4000000000000^3163 ≤ 552623202387^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241847423 10000000000 552623202387 4000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617808487/5000000000 : ℝ)^4187 ≤ (5307568587107/12500000000000 : ℝ)^3163 := by
    have hnat : (2617808487 : ℕ)^4187*12500000000000^3163 ≤ 5307568587107^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617808487 5000000000 5307568587107 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352871341/10000000000 : ℝ), (-2241847423/10000000000 : ℝ), (2617808487/5000000000 : ℝ)] ![(21861935613853/50000000000000 : ℝ), (552623202387/4000000000000 : ℝ), (5307568587107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352871341/10000000000 : ℝ)|^4187 ≤ (21861935613853/50000000000000 : ℝ)^3163
        have hw : |(5352871341/10000000000 : ℝ)|=(5352871341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2241847423/10000000000 : ℝ)|^4187 ≤ (552623202387/4000000000000 : ℝ)^3163
        have hw : |(-2241847423/10000000000 : ℝ)|=(2241847423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617808487/5000000000 : ℝ)|^4187 ≤ (5307568587107/12500000000000 : ℝ)^3163
        have hw : |(2617808487/5000000000 : ℝ)|=(2617808487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338217857/2500000000 : ℝ)*x 0 + (5235616941/10000000000 : ℝ)*x 1 + (-2241847351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338217857/2500000000 : ℝ)^4187 ≤ (21861936084207/50000000000000 : ℝ)^3163 := by
    have hnat : (1338217857 : ℕ)^4187*50000000000000^3163 ≤ 21861936084207^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338217857 2500000000 21861936084207 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235616941/10000000000 : ℝ)^4187 ≤ (8492109668517/20000000000000 : ℝ)^3163 := by
    have hnat : (5235616941 : ℕ)^4187*20000000000000^3163 ≤ 8492109668517^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235616941 10000000000 8492109668517 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241847351/10000000000 : ℝ)^4187 ≤ (6907789736161/50000000000000 : ℝ)^3163 := by
    have hnat : (2241847351 : ℕ)^4187*50000000000000^3163 ≤ 6907789736161^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241847351 10000000000 6907789736161 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338217857/2500000000 : ℝ), (5235616941/10000000000 : ℝ), (-2241847351/10000000000 : ℝ)] ![(21861936084207/50000000000000 : ℝ), (8492109668517/20000000000000 : ℝ), (6907789736161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338217857/2500000000 : ℝ)|^4187 ≤ (21861936084207/50000000000000 : ℝ)^3163
        have hw : |(1338217857/2500000000 : ℝ)|=(1338217857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235616941/10000000000 : ℝ)|^4187 ≤ (8492109668517/20000000000000 : ℝ)^3163
        have hw : |(5235616941/10000000000 : ℝ)|=(5235616941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241847351/10000000000 : ℝ)|^4187 ≤ (6907789736161/50000000000000 : ℝ)^3163
        have hw : |(-2241847351/10000000000 : ℝ)|=(2241847351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178593519/5000000000 : ℝ)*x 0 + (32587209/78125000 : ℝ)*x 1 + (568922517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178593519/5000000000 : ℝ)^4187 ≤ (16648366942267/50000000000000 : ℝ)^3163 := by
    have hnat : (2178593519 : ℕ)^4187*50000000000000^3163 ≤ 16648366942267^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178593519 5000000000 16648366942267 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32587209/78125000 : ℝ)^4187 ≤ (31428086119723/100000000000000 : ℝ)^3163 := by
    have hnat : (32587209 : ℕ)^4187*100000000000000^3163 ≤ 31428086119723^3163*78125000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32587209 78125000 31428086119723 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568922517/1250000000 : ℝ)^4187 ≤ (17637589988007/50000000000000 : ℝ)^3163 := by
    have hnat : (568922517 : ℕ)^4187*50000000000000^3163 ≤ 17637589988007^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568922517 1250000000 17637589988007 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178593519/5000000000 : ℝ), (32587209/78125000 : ℝ), (568922517/1250000000 : ℝ)] ![(16648366942267/50000000000000 : ℝ), (31428086119723/100000000000000 : ℝ), (17637589988007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178593519/5000000000 : ℝ)|^4187 ≤ (16648366942267/50000000000000 : ℝ)^3163
        have hw : |(2178593519/5000000000 : ℝ)|=(2178593519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32587209/78125000 : ℝ)|^4187 ≤ (31428086119723/100000000000000 : ℝ)^3163
        have hw : |(32587209/78125000 : ℝ)|=(32587209/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568922517/1250000000 : ℝ)|^4187 ≤ (17637589988007/50000000000000 : ℝ)^3163
        have hw : |(568922517/1250000000 : ℝ)|=(568922517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072497419/5000000000 : ℝ)*x 0 + (5236333873/10000000000 : ℝ)*x 1 + (542455911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072497419/5000000000 : ℝ)^4187 ≤ (2606213485231/20000000000000 : ℝ)^3163 := by
    have hnat : (1072497419 : ℕ)^4187*20000000000000^3163 ≤ 2606213485231^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072497419 5000000000 2606213485231 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236333873/10000000000 : ℝ)^4187 ≤ (10617061280741/25000000000000 : ℝ)^3163 := by
    have hnat : (5236333873 : ℕ)^4187*25000000000000^3163 ≤ 10617061280741^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236333873 10000000000 10617061280741 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542455911/1000000000 : ℝ)^4187 ≤ (44500687440277/100000000000000 : ℝ)^3163 := by
    have hnat : (542455911 : ℕ)^4187*100000000000000^3163 ≤ 44500687440277^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542455911 1000000000 44500687440277 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072497419/5000000000 : ℝ), (5236333873/10000000000 : ℝ), (542455911/1000000000 : ℝ)] ![(2606213485231/20000000000000 : ℝ), (10617061280741/25000000000000 : ℝ), (44500687440277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072497419/5000000000 : ℝ)|^4187 ≤ (2606213485231/20000000000000 : ℝ)^3163
        have hw : |(-1072497419/5000000000 : ℝ)|=(1072497419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236333873/10000000000 : ℝ)|^4187 ≤ (10617061280741/25000000000000 : ℝ)^3163
        have hw : |(5236333873/10000000000 : ℝ)|=(5236333873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542455911/1000000000 : ℝ)|^4187 ≤ (44500687440277/100000000000000 : ℝ)^3163
        have hw : |(542455911/1000000000 : ℝ)|=(542455911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26523433/50000000 : ℝ)*x 0 + (-2052905053/10000000000 : ℝ)*x 1 + (1084911813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26523433/50000000 : ℝ)^4187 ≤ (1080090577359/2500000000000 : ℝ)^3163 := by
    have hnat : (26523433 : ℕ)^4187*2500000000000^3163 ≤ 1080090577359^3163*50000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26523433 50000000 1080090577359 2500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052905053/10000000000 : ℝ)^4187 ≤ (12295689939409/100000000000000 : ℝ)^3163 := by
    have hnat : (2052905053 : ℕ)^4187*100000000000000^3163 ≤ 12295689939409^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052905053 10000000000 12295689939409 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084911813/2000000000 : ℝ)^4187 ≤ (11125171737901/25000000000000 : ℝ)^3163 := by
    have hnat : (1084911813 : ℕ)^4187*25000000000000^3163 ≤ 11125171737901^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084911813 2000000000 11125171737901 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26523433/50000000 : ℝ), (-2052905053/10000000000 : ℝ), (1084911813/2000000000 : ℝ)] ![(1080090577359/2500000000000 : ℝ), (12295689939409/100000000000000 : ℝ), (11125171737901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26523433/50000000 : ℝ)|^4187 ≤ (1080090577359/2500000000000 : ℝ)^3163
        have hw : |(26523433/50000000 : ℝ)|=(26523433/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052905053/10000000000 : ℝ)|^4187 ≤ (12295689939409/100000000000000 : ℝ)^3163
        have hw : |(-2052905053/10000000000 : ℝ)|=(2052905053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084911813/2000000000 : ℝ)|^4187 ≤ (11125171737901/25000000000000 : ℝ)^3163
        have hw : |(1084911813/2000000000 : ℝ)|=(1084911813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304686269/10000000000 : ℝ)*x 0 + (5424559429/10000000000 : ℝ)*x 1 + (-513226251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304686269/10000000000 : ℝ)^4187 ≤ (21601809762903/50000000000000 : ℝ)^3163 := by
    have hnat : (5304686269 : ℕ)^4187*50000000000000^3163 ≤ 21601809762903^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304686269 10000000000 21601809762903 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424559429/10000000000 : ℝ)^4187 ≤ (11125172726107/25000000000000 : ℝ)^3163 := by
    have hnat : (5424559429 : ℕ)^4187*25000000000000^3163 ≤ 11125172726107^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424559429 10000000000 11125172726107 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513226251/2500000000 : ℝ)^4187 ≤ (2459137910183/20000000000000 : ℝ)^3163 := by
    have hnat : (513226251 : ℕ)^4187*20000000000000^3163 ≤ 2459137910183^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513226251 2500000000 2459137910183 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304686269/10000000000 : ℝ), (5424559429/10000000000 : ℝ), (-513226251/2500000000 : ℝ)] ![(21601809762903/50000000000000 : ℝ), (11125172726107/25000000000000 : ℝ), (2459137910183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304686269/10000000000 : ℝ)|^4187 ≤ (21601809762903/50000000000000 : ℝ)^3163
        have hw : |(5304686269/10000000000 : ℝ)|=(5304686269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424559429/10000000000 : ℝ)|^4187 ≤ (11125172726107/25000000000000 : ℝ)^3163
        have hw : |(5424559429/10000000000 : ℝ)|=(5424559429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513226251/2500000000 : ℝ)|^4187 ≤ (2459137910183/20000000000000 : ℝ)^3163
        have hw : |(-513226251/2500000000 : ℝ)|=(513226251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s3_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174288799/400000000 : ℝ)*x 0 + (2274971517/5000000000 : ℝ)*x 1 + (2086303729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174288799/400000000 : ℝ)^4187 ≤ (16648533534127/50000000000000 : ℝ)^3163 := by
    have hnat : (174288799 : ℕ)^4187*50000000000000^3163 ≤ 16648533534127^3163*400000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174288799 400000000 16648533534127 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274971517/5000000000 : ℝ)^4187 ≤ (2203777291001/6250000000000 : ℝ)^3163 := by
    have hnat : (2274971517 : ℕ)^4187*6250000000000^3163 ≤ 2203777291001^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274971517 5000000000 2203777291001 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086303729/5000000000 : ℝ)^4187 ≤ (31442496266039/100000000000000 : ℝ)^3163 := by
    have hnat : (2086303729 : ℕ)^4187*100000000000000^3163 ≤ 31442496266039^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086303729 5000000000 31442496266039 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174288799/400000000 : ℝ), (2274971517/5000000000 : ℝ), (2086303729/5000000000 : ℝ)] ![(16648533534127/50000000000000 : ℝ), (2203777291001/6250000000000 : ℝ), (31442496266039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174288799/400000000 : ℝ)|^4187 ≤ (16648533534127/50000000000000 : ℝ)^3163
        have hw : |(174288799/400000000 : ℝ)|=(174288799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2274971517/5000000000 : ℝ)|^4187 ≤ (2203777291001/6250000000000 : ℝ)^3163
        have hw : |(2274971517/5000000000 : ℝ)|=(2274971517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086303729/5000000000 : ℝ)|^4187 ≤ (31442496266039/100000000000000 : ℝ)^3163
        have hw : |(2086303729/5000000000 : ℝ)|=(2086303729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2687/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16389/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16389/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16389/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16389/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16389/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16389/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9243/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (5913593829980899/100000000000000000000 : ℝ) := by
    have hpowers : (9243/100000 : ℝ)^8373 ≤ (5913593829980899/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9243 : ℕ)^8373*100000000000000000000^2048 ≤ 5913593829980899^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9243 100000 5913593829980899 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9243/100000 : ℝ)) (X := (5913593829980899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16389/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (61488348134460771/100000000000000000000 : ℝ) := by
    have hpowers : (16389/100000 : ℝ)^8373 ≤ (61488348134460771/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16389 : ℕ)^8373*100000000000000000000^2048 ≤ 61488348134460771^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16389 100000 61488348134460771 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16389/100000 : ℝ)) (X := (61488348134460771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005913593829980899/50000000000000000000 : ℝ) ≤ (1000028927503123/1000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50005913593829980899/50000000000000000000 : ℝ)^2048 ≤ (1000028927503123/1000000000000000 : ℝ)^8373 := by
      have hnat : (50005913593829980899 : ℕ)^2048*1000000000000000^8373 ≤ 1000028927503123^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005913593829980899 50000000000000000000 1000028927503123 1000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028927503123/1000000000000000 : ℝ)) (X := (50005913593829980899/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006740194196444167/10000000000000000000 : ℝ) ≤ (1000164820314319/1000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (10006740194196444167/10000000000000000000 : ℝ)^2048 ≤ (1000164820314319/1000000000000000 : ℝ)^8373 := by
      have hnat : (10006740194196444167 : ℕ)^2048*1000000000000000^8373 ≤ 1000164820314319^8373*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006740194196444167 10000000000000000000 1000164820314319 1000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000164820314319/1000000000000000 : ℝ)) (X := (10006740194196444167/10000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50061488348134460771/50000000000000000000 : ℝ) ≤ (200060142625103/200000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50061488348134460771/50000000000000000000 : ℝ)^2048 ≤ (200060142625103/200000000000000 : ℝ)^8373 := by
      have hnat : (50061488348134460771 : ℕ)^2048*200000000000000^8373 ≤ 200060142625103^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061488348134460771 50000000000000000000 200060142625103 200000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200060142625103/200000000000000 : ℝ)) (X := (50061488348134460771/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5913593829980899/100000000000000000000 : ℝ) ≤ ((396871922301641539/397000000000000000 : ℝ)+2*(3774800311/1985000000000 : ℝ)*(9243/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (396871922301641539/397000000000000000 : ℝ)+2*(3774800311/1985000000000 : ℝ)*(9243/100000 : ℝ)=(1000028927503123/1000000000000000 : ℝ) by norm_num, show 1+2*(5913593829980899/100000000000000000000 : ℝ)=(50005913593829980899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61488348134460771/100000000000000000000 : ℝ)+(5913593829980899/100000000000000000000 : ℝ) ≤ ((396871922301641539/397000000000000000 : ℝ)+(3774800311/1985000000000 : ℝ)*((16389/100000 : ℝ)+(9243/100000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (396871922301641539/397000000000000000 : ℝ)+(3774800311/1985000000000 : ℝ)*((16389/100000 : ℝ)+(9243/100000 : ℝ))=(1000164820314319/1000000000000000 : ℝ) by norm_num, show 1+(61488348134460771/100000000000000000000 : ℝ)+(5913593829980899/100000000000000000000 : ℝ)=(10006740194196444167/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61488348134460771/100000000000000000000 : ℝ) ≤ ((396871922301641539/397000000000000000 : ℝ)+2*(3774800311/1985000000000 : ℝ)*(16389/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (396871922301641539/397000000000000000 : ℝ)+2*(3774800311/1985000000000 : ℝ)*(16389/100000 : ℝ)=(200060142625103/200000000000000 : ℝ) by norm_num, show 1+2*(61488348134460771/100000000000000000000 : ℝ)=(50061488348134460771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (396871922301641539/397000000000000000 : ℝ)*(X 1 0+X 2 0)+(3774800311/1985000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (9243/100000 : ℝ)) (hi := (16389/100000 : ℝ)) (c := (396871922301641539/397000000000000000 : ℝ)) (alpha := (3774800311/1985000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (396871922301641539/397000000000000000 : ℝ)*(X 0 1+X 2 1)+(3774800311/1985000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (9243/100000 : ℝ)) (hi := (16389/100000 : ℝ)) (c := (396871922301641539/397000000000000000 : ℝ)) (alpha := (3774800311/1985000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (396871922301641539/397000000000000000 : ℝ)*(X 0 2+X 1 2)+(3774800311/1985000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (9243/100000 : ℝ)) (hi := (16389/100000 : ℝ)) (c := (396871922301641539/397000000000000000 : ℝ)) (alpha := (3774800311/1985000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2144978547/10000000000 : ℝ)*X 0 0+(2712639849/5000000000 : ℝ)*X 0 1+(523561717/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352871341/10000000000 : ℝ)*X 1 0+(-2241847423/10000000000 : ℝ)*X 1 1+(2617808487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338217857/2500000000 : ℝ)*X 2 0+(5235616941/10000000000 : ℝ)*X 2 1+(-2241847351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178593519/5000000000 : ℝ)*X 0 0+(32587209/78125000 : ℝ)*X 0 1+(568922517/1250000000 : ℝ)*X 0 2+(2178593519/5000000000 : ℝ)*X 1 0+(32587209/78125000 : ℝ)*X 1 1+(568922517/1250000000 : ℝ)*X 1 2+(2178593519/5000000000 : ℝ)*X 2 0+(32587209/78125000 : ℝ)*X 2 1+(568922517/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072497419/5000000000 : ℝ)*X 0 0+(5236333873/10000000000 : ℝ)*X 0 1+(542455911/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((26523433/50000000 : ℝ)*X 1 0+(-2052905053/10000000000 : ℝ)*X 1 1+(1084911813/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304686269/10000000000 : ℝ)*X 2 0+(5424559429/10000000000 : ℝ)*X 2 1+(-513226251/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174288799/400000000 : ℝ)*X 0 0+(2274971517/5000000000 : ℝ)*X 0 1+(2086303729/5000000000 : ℝ)*X 0 2+(174288799/400000000 : ℝ)*X 1 0+(2274971517/5000000000 : ℝ)*X 1 1+(2086303729/5000000000 : ℝ)*X 1 2+(174288799/400000000 : ℝ)*X 2 0+(2274971517/5000000000 : ℝ)*X 2 1+(2086303729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1118255993247058698267069/794000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106617109/20000000000000 : ℝ)*(base19) + (141478901/25000000000000 : ℝ)*(base23) + (28297533/100000000000000 : ℝ)*(lower2) + (15081531/100000000000000 : ℝ)*(upper3) + (70313397/100000000000000 : ℝ)*(upper5) + (158052297770757/4000000000000 : ℝ)*(major0) + (158052297770757/4000000000000 : ℝ)*(major1) + (158052297770757/4000000000000 : ℝ)*(major2) + (659065862335459/12500000000000 : ℝ)*(sp0) + (5272533540245217/100000000000000 : ℝ)*(sp1) + (2636266753707579/50000000000000 : ℝ)*(sp2) + (657519423036293/25000000000000 : ℝ)*(sp3) + (717464709/10000000000000 : ℝ)*(sp4) + (3076115811/100000000000000 : ℝ)*(sp7) + (328760096032623/12500000000000 : ℝ)*(f.failure) + (2636267036665381/50000000000000 : ℝ)*(f.sum) + (2231673737671/397000000000000000000000000 : ℝ)*base65 + (6535398999796977/1588000000000000000000000000000 : ℝ)*base68 + (5973046063715023/1588000000000000000000000000000 : ℝ)*base69 + (14916095541628977/1588000000000000000000000000000 : ℝ)*base72 + (2038763946281/397000000000000000000000000 : ℝ)*base73 + (16086739817531023/1588000000000000000000000000000 : ℝ)*base75 + (19998774789304977/1588000000000000000000000000000 : ℝ)*base78 + (18495295630372977/1588000000000000000000000000000 : ℝ)*base80 + (153236251251/24812500000000000000000000 : ℝ)*base81 + (8853699/1250000000000000000000 : ℝ)*base89 + (8853699/1250000000000000000000 : ℝ)*base91 + (8853699/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43891154813639475817033137/19850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1011696627/100000000000000 : ℝ)*(base19) + (898037593/100000000000000 : ℝ)*(base23) + (40167703/100000000000000 : ℝ)*(upper3) + (107948591/100000000000000 : ℝ)*(lower4) + (129167687/100000000000000 : ℝ)*(upper5) + (3981470289719561/100000000000000 : ℝ)*(major0) + (3981470289719561/100000000000000 : ℝ)*(major1) + (3981470289719561/100000000000000 : ℝ)*(major2) + (21108085989/100000000000000 : ℝ)*(sp1) + (567190697/2500000000000 : ℝ)*(sp2) + (5312782656442739/100000000000000 : ℝ)*(sp4) + (5312760536660123/100000000000000 : ℝ)*(sp5) + (2656379535388633/50000000000000 : ℝ)*(sp6) + (2650157849291671/100000000000000 : ℝ)*(sp7) + (2650157849291671/100000000000000 : ℝ)*(f.failure) + (5312782656442739/100000000000000 : ℝ)*(f.sum) + (130382202487/397000000000000000000000000 : ℝ)*base66 + (2720205099055621/39700000000000000000000000000000 : ℝ)*base68 + (31417164015044379/39700000000000000000000000000000 : ℝ)*base69 + (83351248374844379/39700000000000000000000000000000 : ℝ)*base71 + (29874452829/12406250000000000000000000 : ℝ)*base73 + (272996083627655621/39700000000000000000000000000000 : ℝ)*base76 + (33429483381655621/39700000000000000000000000000000 : ℝ)*base78 + (17030389564955621/39700000000000000000000000000000 : ℝ)*base80 + (380530638203/198500000000000000000000000 : ℝ)*base81 + (8189077/10000000000000000000000 : ℝ)*base90 + (8189077/10000000000000000000000 : ℝ)*base92 + (8189077/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1181_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2687/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1181_s4_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147680559/10000000000 : ℝ)*x 0 + (5400080419/10000000000 : ℝ)*x 1 + (2629523911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147680559/10000000000 : ℝ)^4187 ≤ (522106801779/4000000000000 : ℝ)^3163 := by
    have hnat : (2147680559 : ℕ)^4187*4000000000000^3163 ≤ 522106801779^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147680559 10000000000 522106801779 4000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400080419/10000000000 : ℝ)^4187 ≤ (2211752889199/5000000000000 : ℝ)^3163 := by
    have hnat : (5400080419 : ℕ)^4187*5000000000000^3163 ≤ 2211752889199^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400080419 10000000000 2211752889199 5000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629523911/5000000000 : ℝ)^4187 ≤ (42712272156609/100000000000000 : ℝ)^3163 := by
    have hnat : (2629523911 : ℕ)^4187*100000000000000^3163 ≤ 42712272156609^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629523911 5000000000 42712272156609 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147680559/10000000000 : ℝ), (5400080419/10000000000 : ℝ), (2629523911/5000000000 : ℝ)] ![(522106801779/4000000000000 : ℝ), (2211752889199/5000000000000 : ℝ), (42712272156609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147680559/10000000000 : ℝ)|^4187 ≤ (522106801779/4000000000000 : ℝ)^3163
        have hw : |(-2147680559/10000000000 : ℝ)|=(2147680559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400080419/10000000000 : ℝ)|^4187 ≤ (2211752889199/5000000000000 : ℝ)^3163
        have hw : |(5400080419/10000000000 : ℝ)|=(5400080419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629523911/5000000000 : ℝ)|^4187 ≤ (42712272156609/100000000000000 : ℝ)^3163
        have hw : |(2629523911/5000000000 : ℝ)|=(2629523911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346554463/10000000000 : ℝ)*x 0 + (-2219325219/10000000000 : ℝ)*x 1 + (1314761857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346554463/10000000000 : ℝ)^4187 ≤ (43655581548997/100000000000000 : ℝ)^3163 := by
    have hnat : (5346554463 : ℕ)^4187*100000000000000^3163 ≤ 43655581548997^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346554463 10000000000 43655581548997 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219325219/10000000000 : ℝ)^4187 ≤ (13632150512931/100000000000000 : ℝ)^3163 := by
    have hnat : (2219325219 : ℕ)^4187*100000000000000^3163 ≤ 13632150512931^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219325219 10000000000 13632150512931 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314761857/2500000000 : ℝ)^4187 ≤ (42712267920711/100000000000000 : ℝ)^3163 := by
    have hnat : (1314761857 : ℕ)^4187*100000000000000^3163 ≤ 42712267920711^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314761857 2500000000 42712267920711 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346554463/10000000000 : ℝ), (-2219325219/10000000000 : ℝ), (1314761857/2500000000 : ℝ)] ![(43655581548997/100000000000000 : ℝ), (13632150512931/100000000000000 : ℝ), (42712267920711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346554463/10000000000 : ℝ)|^4187 ≤ (43655581548997/100000000000000 : ℝ)^3163
        have hw : |(5346554463/10000000000 : ℝ)|=(5346554463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219325219/10000000000 : ℝ)|^4187 ≤ (13632150512931/100000000000000 : ℝ)^3163
        have hw : |(-2219325219/10000000000 : ℝ)|=(2219325219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314761857/2500000000 : ℝ)|^4187 ≤ (42712267920711/100000000000000 : ℝ)^3163
        have hw : |(1314761857/2500000000 : ℝ)|=(1314761857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346554971/10000000000 : ℝ)*x 0 + (2629523349/5000000000 : ℝ)*x 1 + (-221932551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346554971/10000000000 : ℝ)^4187 ≤ (5456948379971/12500000000000 : ℝ)^3163 := by
    have hnat : (5346554971 : ℕ)^4187*12500000000000^3163 ≤ 5456948379971^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346554971 10000000000 5456948379971 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629523349/5000000000 : ℝ)^4187 ≤ (42712260072473/100000000000000 : ℝ)^3163 := by
    have hnat : (2629523349 : ℕ)^4187*100000000000000^3163 ≤ 42712260072473^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629523349 5000000000 42712260072473 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221932551/1000000000 : ℝ)^4187 ≤ (1363215287907/10000000000000 : ℝ)^3163 := by
    have hnat : (221932551 : ℕ)^4187*10000000000000^3163 ≤ 1363215287907^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221932551 1000000000 1363215287907 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346554971/10000000000 : ℝ), (2629523349/5000000000 : ℝ), (-221932551/1000000000 : ℝ)] ![(5456948379971/12500000000000 : ℝ), (42712260072473/100000000000000 : ℝ), (1363215287907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346554971/10000000000 : ℝ)|^4187 ≤ (5456948379971/12500000000000 : ℝ)^3163
        have hw : |(5346554971/10000000000 : ℝ)|=(5346554971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629523349/5000000000 : ℝ)|^4187 ≤ (42712260072473/100000000000000 : ℝ)^3163
        have hw : |(2629523349/5000000000 : ℝ)|=(2629523349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221932551/1000000000 : ℝ)|^4187 ≤ (1363215287907/10000000000000 : ℝ)^3163
        have hw : |(-221932551/1000000000 : ℝ)|=(221932551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179401633/5000000000 : ℝ)*x 0 + (2109849043/5000000000 : ℝ)*x 1 + (225121431/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179401633/5000000000 : ℝ)^4187 ≤ (16656542133219/50000000000000 : ℝ)^3163 := by
    have hnat : (2179401633 : ℕ)^4187*50000000000000^3163 ≤ 16656542133219^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179401633 5000000000 16656542133219 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109849043/5000000000 : ℝ)^4187 ≤ (31913081603927/100000000000000 : ℝ)^3163 := by
    have hnat : (2109849043 : ℕ)^4187*100000000000000^3163 ≤ 31913081603927^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109849043 5000000000 31913081603927 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225121431/500000000 : ℝ)^4187 ≤ (34773834105593/100000000000000 : ℝ)^3163 := by
    have hnat : (225121431 : ℕ)^4187*100000000000000^3163 ≤ 34773834105593^3163*500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225121431 500000000 34773834105593 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179401633/5000000000 : ℝ), (2109849043/5000000000 : ℝ), (225121431/500000000 : ℝ)] ![(16656542133219/50000000000000 : ℝ), (31913081603927/100000000000000 : ℝ), (34773834105593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179401633/5000000000 : ℝ)|^4187 ≤ (16656542133219/50000000000000 : ℝ)^3163
        have hw : |(2179401633/5000000000 : ℝ)|=(2179401633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2109849043/5000000000 : ℝ)|^4187 ≤ (31913081603927/100000000000000 : ℝ)^3163
        have hw : |(2109849043/5000000000 : ℝ)|=(2109849043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225121431/500000000 : ℝ)|^4187 ≤ (34773834105593/100000000000000 : ℝ)^3163
        have hw : |(225121431/500000000 : ℝ)|=(225121431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147687783/10000000000 : ℝ)*x 0 + (1314861087/2500000000 : ℝ)*x 1 + (2699840953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147687783/10000000000 : ℝ)^4187 ≤ (815795510161/6250000000000 : ℝ)^3163 := by
    have hnat : (2147687783 : ℕ)^4187*6250000000000^3163 ≤ 815795510161^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147687783 10000000000 815795510161 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314861087/2500000000 : ℝ)^4187 ≤ (21358267632101/50000000000000 : ℝ)^3163 := by
    have hnat : (1314861087 : ℕ)^4187*50000000000000^3163 ≤ 21358267632101^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314861087 2500000000 21358267632101 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699840953/5000000000 : ℝ)^4187 ≤ (44230736553353/100000000000000 : ℝ)^3163 := by
    have hnat : (2699840953 : ℕ)^4187*100000000000000^3163 ≤ 44230736553353^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699840953 5000000000 44230736553353 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147687783/10000000000 : ℝ), (1314861087/2500000000 : ℝ), (2699840953/5000000000 : ℝ)] ![(815795510161/6250000000000 : ℝ), (21358267632101/50000000000000 : ℝ), (44230736553353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147687783/10000000000 : ℝ)|^4187 ≤ (815795510161/6250000000000 : ℝ)^3163
        have hw : |(-2147687783/10000000000 : ℝ)|=(2147687783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314861087/2500000000 : ℝ)|^4187 ≤ (21358267632101/50000000000000 : ℝ)^3163
        have hw : |(1314861087/2500000000 : ℝ)|=(1314861087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699840953/5000000000 : ℝ)|^4187 ≤ (44230736553353/100000000000000 : ℝ)^3163
        have hw : |(2699840953/5000000000 : ℝ)|=(2699840953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655361857/5000000000 : ℝ)*x 0 + (-415738111/2000000000 : ℝ)*x 1 + (5399681739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655361857/5000000000 : ℝ)^4187 ≤ (43268721981141/100000000000000 : ℝ)^3163 := by
    have hnat : (2655361857 : ℕ)^4187*100000000000000^3163 ≤ 43268721981141^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655361857 5000000000 43268721981141 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415738111/2000000000 : ℝ)^4187 ≤ (3125135816749/25000000000000 : ℝ)^3163 := by
    have hnat : (415738111 : ℕ)^4187*25000000000000^3163 ≤ 3125135816749^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415738111 2000000000 3125135816749 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399681739/10000000000 : ℝ)^4187 ≤ (44230734742529/100000000000000 : ℝ)^3163 := by
    have hnat : (5399681739 : ℕ)^4187*100000000000000^3163 ≤ 44230734742529^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399681739 10000000000 44230734742529 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655361857/5000000000 : ℝ), (-415738111/2000000000 : ℝ), (5399681739/10000000000 : ℝ)] ![(43268721981141/100000000000000 : ℝ), (3125135816749/25000000000000 : ℝ), (44230734742529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655361857/5000000000 : ℝ)|^4187 ≤ (43268721981141/100000000000000 : ℝ)^3163
        have hw : |(2655361857/5000000000 : ℝ)|=(2655361857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415738111/2000000000 : ℝ)|^4187 ≤ (3125135816749/25000000000000 : ℝ)^3163
        have hw : |(-415738111/2000000000 : ℝ)|=(415738111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399681739/10000000000 : ℝ)|^4187 ≤ (44230734742529/100000000000000 : ℝ)^3163
        have hw : |(5399681739/10000000000 : ℝ)|=(5399681739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310723149/10000000000 : ℝ)*x 0 + (5399682431/10000000000 : ℝ)*x 1 + (-2078690377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310723149/10000000000 : ℝ)^4187 ≤ (1081717897189/2500000000000 : ℝ)^3163 := by
    have hnat : (5310723149 : ℕ)^4187*2500000000000^3163 ≤ 1081717897189^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310723149 10000000000 1081717897189 2500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399682431/10000000000 : ℝ)^4187 ≤ (44230742246063/100000000000000 : ℝ)^3163 := by
    have hnat : (5399682431 : ℕ)^4187*100000000000000^3163 ≤ 44230742246063^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399682431 10000000000 44230742246063 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078690377/10000000000 : ℝ)^4187 ≤ (12500541850019/100000000000000 : ℝ)^3163 := by
    have hnat : (2078690377 : ℕ)^4187*100000000000000^3163 ≤ 12500541850019^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078690377 10000000000 12500541850019 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310723149/10000000000 : ℝ), (5399682431/10000000000 : ℝ), (-2078690377/10000000000 : ℝ)] ![(1081717897189/2500000000000 : ℝ), (44230742246063/100000000000000 : ℝ), (12500541850019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310723149/10000000000 : ℝ)|^4187 ≤ (1081717897189/2500000000000 : ℝ)^3163
        have hw : |(5310723149/10000000000 : ℝ)|=(5310723149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399682431/10000000000 : ℝ)|^4187 ≤ (44230742246063/100000000000000 : ℝ)^3163
        have hw : |(5399682431/10000000000 : ℝ)|=(5399682431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078690377/10000000000 : ℝ)|^4187 ≤ (12500541850019/100000000000000 : ℝ)^3163
        have hw : |(-2078690377/10000000000 : ℝ)|=(2078690377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s4_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4358817091/10000000000 : ℝ)*x 0 + (4501632827/10000000000 : ℝ)*x 1 + (2110248373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358817091/10000000000 : ℝ)^4187 ≤ (2082076508369/6250000000000 : ℝ)^3163 := by
    have hnat : (4358817091 : ℕ)^4187*6250000000000^3163 ≤ 2082076508369^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358817091 10000000000 2082076508369 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501632827/10000000000 : ℝ)^4187 ≤ (17382849181503/50000000000000 : ℝ)^3163 := by
    have hnat : (4501632827 : ℕ)^4187*50000000000000^3163 ≤ 17382849181503^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501632827 10000000000 17382849181503 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110248373/5000000000 : ℝ)^4187 ≤ (31921077485839/100000000000000 : ℝ)^3163 := by
    have hnat : (2110248373 : ℕ)^4187*100000000000000^3163 ≤ 31921077485839^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110248373 5000000000 31921077485839 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358817091/10000000000 : ℝ), (4501632827/10000000000 : ℝ), (2110248373/5000000000 : ℝ)] ![(2082076508369/6250000000000 : ℝ), (17382849181503/50000000000000 : ℝ), (31921077485839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358817091/10000000000 : ℝ)|^4187 ≤ (2082076508369/6250000000000 : ℝ)^3163
        have hw : |(4358817091/10000000000 : ℝ)|=(4358817091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501632827/10000000000 : ℝ)|^4187 ≤ (17382849181503/50000000000000 : ℝ)^3163
        have hw : |(4501632827/10000000000 : ℝ)|=(4501632827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110248373/5000000000 : ℝ)|^4187 ≤ (31921077485839/100000000000000 : ℝ)^3163
        have hw : |(2110248373/5000000000 : ℝ)|=(2110248373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2687/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11247/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2687/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2687/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2687/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2687/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2687/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2687/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2687/25000 : ℝ) ^ (8373/2048 : ℝ) ≤ (2191444239101657/20000000000000000000 : ℝ) := by
    have hpowers : (2687/25000 : ℝ)^8373 ≤ (2191444239101657/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2687 : ℕ)^8373*20000000000000000000^2048 ≤ 2191444239101657^2048*25000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2687 25000 2191444239101657 20000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2687/25000 : ℝ)) (X := (2191444239101657/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (40089485475739819/100000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^8373 ≤ (40089485475739819/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14761 : ℕ)^8373*100000000000000000000^2048 ≤ 40089485475739819^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 40089485475739819 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (40089485475739819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002191444239101657/10000000000000000000 : ℝ) ≤ (5000267986764911/5000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (10002191444239101657/10000000000000000000 : ℝ)^2048 ≤ (5000267986764911/5000000000000000 : ℝ)^8373 := by
      have hnat : (10002191444239101657 : ℕ)^2048*5000000000000000^8373 ≤ 5000267986764911^8373*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002191444239101657 10000000000000000000 5000267986764911 5000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000267986764911/5000000000000000 : ℝ)) (X := (10002191444239101657/10000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506380838333906013/12500000000000000000 : ℝ) ≤ (10001248339959319/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (12506380838333906013/12500000000000000000 : ℝ)^2048 ≤ (10001248339959319/10000000000000000 : ℝ)^8373 := by
      have hnat : (12506380838333906013 : ℕ)^2048*10000000000000000^8373 ≤ 10001248339959319^8373*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506380838333906013 12500000000000000000 10001248339959319 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001248339959319/10000000000000000 : ℝ)) (X := (12506380838333906013/12500000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040089485475739819/50000000000000000000 : ℝ) ≤ (625122544149301/625000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50040089485475739819/50000000000000000000 : ℝ)^2048 ≤ (625122544149301/625000000000000 : ℝ)^8373 := by
      have hnat : (50040089485475739819 : ℕ)^2048*625000000000000^8373 ≤ 625122544149301^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040089485475739819 50000000000000000000 625122544149301 625000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625122544149301/625000000000000 : ℝ)) (X := (50040089485475739819/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2191444239101657/20000000000000000000 : ℝ) ≤ ((20058418916503354087/20065000000000000000 : ℝ)+2*(712366429497/401300000000000 : ℝ)*(2687/25000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (20058418916503354087/20065000000000000000 : ℝ)+2*(712366429497/401300000000000 : ℝ)*(2687/25000 : ℝ)=(5000267986764911/5000000000000000 : ℝ) by norm_num, show 1+2*(2191444239101657/20000000000000000000 : ℝ)=(10002191444239101657/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40089485475739819/100000000000000000000 : ℝ)+(2191444239101657/20000000000000000000 : ℝ) ≤ ((20058418916503354087/20065000000000000000 : ℝ)+(712366429497/401300000000000 : ℝ)*((14761/100000 : ℝ)+(2687/25000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (20058418916503354087/20065000000000000000 : ℝ)+(712366429497/401300000000000 : ℝ)*((14761/100000 : ℝ)+(2687/25000 : ℝ))=(10001248339959319/10000000000000000 : ℝ) by norm_num, show 1+(40089485475739819/100000000000000000000 : ℝ)+(2191444239101657/20000000000000000000 : ℝ)=(12506380838333906013/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40089485475739819/100000000000000000000 : ℝ) ≤ ((20058418916503354087/20065000000000000000 : ℝ)+2*(712366429497/401300000000000 : ℝ)*(14761/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (20058418916503354087/20065000000000000000 : ℝ)+2*(712366429497/401300000000000 : ℝ)*(14761/100000 : ℝ)=(625122544149301/625000000000000 : ℝ) by norm_num, show 1+2*(40089485475739819/100000000000000000000 : ℝ)=(50040089485475739819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20058418916503354087/20065000000000000000 : ℝ)*(X 1 0+X 2 0)+(712366429497/401300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (2687/25000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (20058418916503354087/20065000000000000000 : ℝ)) (alpha := (712366429497/401300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20058418916503354087/20065000000000000000 : ℝ)*(X 0 1+X 2 1)+(712366429497/401300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (2687/25000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (20058418916503354087/20065000000000000000 : ℝ)) (alpha := (712366429497/401300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20058418916503354087/20065000000000000000 : ℝ)*(X 0 2+X 1 2)+(712366429497/401300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (2687/25000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (20058418916503354087/20065000000000000000 : ℝ)) (alpha := (712366429497/401300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2147680559/10000000000 : ℝ)*X 0 0+(5400080419/10000000000 : ℝ)*X 0 1+(2629523911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346554463/10000000000 : ℝ)*X 1 0+(-2219325219/10000000000 : ℝ)*X 1 1+(1314761857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346554971/10000000000 : ℝ)*X 2 0+(2629523349/5000000000 : ℝ)*X 2 1+(-221932551/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179401633/5000000000 : ℝ)*X 0 0+(2109849043/5000000000 : ℝ)*X 0 1+(225121431/500000000 : ℝ)*X 0 2+(2179401633/5000000000 : ℝ)*X 1 0+(2109849043/5000000000 : ℝ)*X 1 1+(225121431/500000000 : ℝ)*X 1 2+(2179401633/5000000000 : ℝ)*X 2 0+(2109849043/5000000000 : ℝ)*X 2 1+(225121431/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2147687783/10000000000 : ℝ)*X 0 0+(1314861087/2500000000 : ℝ)*X 0 1+(2699840953/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655361857/5000000000 : ℝ)*X 1 0+(-415738111/2000000000 : ℝ)*X 1 1+(5399681739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310723149/10000000000 : ℝ)*X 2 0+(5399682431/10000000000 : ℝ)*X 2 1+(-2078690377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358817091/10000000000 : ℝ)*X 0 0+(4501632827/10000000000 : ℝ)*X 0 1+(2110248373/5000000000 : ℝ)*X 0 2+(4358817091/10000000000 : ℝ)*X 1 0+(4501632827/10000000000 : ℝ)*X 1 1+(2110248373/5000000000 : ℝ)*X 1 2+(4358817091/10000000000 : ℝ)*X 2 0+(4501632827/10000000000 : ℝ)*X 2 1+(2110248373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2812003817811314864486024991/200650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117853057/20000000000000 : ℝ)*(base19) + (1663181683/100000000000000 : ℝ)*(base23) + (22607421/20000000000000 : ℝ)*(lower2) + (336522803/100000000000000 : ℝ)*(lower4) + (43504419/50000000000000 : ℝ)*(upper5) + (1062751416189069/20000000000000 : ℝ)*(major0) + (1062751416189069/20000000000000 : ℝ)*(major1) + (1062751416189069/20000000000000 : ℝ)*(major2) + (7090555231518113/100000000000000 : ℝ)*(sp0) + (7090554642252827/100000000000000 : ℝ)*(sp1) + (7090550914112661/100000000000000 : ℝ)*(sp2) + (884236965245339/25000000000000 : ℝ)*(sp3) + (331777971/12500000000000 : ℝ)*(sp6) + (10602242139/100000000000000 : ℝ)*(sp7) + (442119807902937/12500000000000 : ℝ)*(f.failure) + (7090555231518113/100000000000000 : ℝ)*(f.sum) + (73395960320979/4013000000000000000000000000 : ℝ)*base65 + (6055978672330274997/401300000000000000000000000000000 : ℝ)*base68 + (2578361073470525003/401300000000000000000000000000000 : ℝ)*base69 + (6531352699640725003/401300000000000000000000000000000 : ℝ)*base71 + (2367868428527/802600000000000000000000000 : ℝ)*base74 + (1762165402679525003/401300000000000000000000000000000 : ℝ)*base75 + (3121917385570125003/401300000000000000000000000000000 : ℝ)*base77 + (4366158162180974997/401300000000000000000000000000000 : ℝ)*base80 + (16622791238691/4013000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11020581/1250000000000000000000 : ℝ)*base89 + (11020581/1250000000000000000000 : ℝ)*base91 + (11020581/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (746380939963461021611695623/125406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (803997081/100000000000000 : ℝ)*(base19) + (20480111/100000000000000 : ℝ)*(base23) + (106828891/100000000000000 : ℝ)*(lower2) + (125390433/50000000000000 : ℝ)*(upper3) + (2664073/5000000000000 : ℝ)*(lower4) + (667984105894307/12500000000000 : ℝ)*(major0) + (667984105894307/12500000000000 : ℝ)*(major1) + (667984105894307/12500000000000 : ℝ)*(major2) + (2251077037/20000000000000 : ℝ)*(sp2) + (183712899/6250000000000 : ℝ)*(sp3) + (7130741288686423/100000000000000 : ℝ)*(sp4) + (3565370242344671/50000000000000 : ℝ)*(sp5) + (7130730012821127/100000000000000 : ℝ)*(sp6) + (889250316956487/25000000000000 : ℝ)*(sp7) + (889251051808083/25000000000000 : ℝ)*(f.failure) + (7130741288686423/100000000000000 : ℝ)*(f.sum) + (98487380610437/20065000000000000000000000000 : ℝ)*base65 + (105186503527932709/250812500000000000000000000000000 : ℝ)*base67 + (1952778148907557709/250812500000000000000000000000000 : ℝ)*base69 + (196420638277567291/250812500000000000000000000000000 : ℝ)*base72 + (37058677229991/10032500000000000000000000000 : ℝ)*base73 + (2378064978563807709/250812500000000000000000000000000 : ℝ)*base75 + (3602330967609307709/250812500000000000000000000000000 : ℝ)*base77 + (473739326073254791/250812500000000000000000000000000 : ℝ)*base80 + (51114327010203/20065000000000000000000000000 : ℝ)*base82 + (15373321/2500000000000000000000 : ℝ)*base90 + (15373321/2500000000000000000000 : ℝ)*base92 + (15373321/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1181_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2687/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1181_s5_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-537059853/2500000000 : ℝ)*x 0 + (5393909249/10000000000 : ℝ)*x 1 + (658106461/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537059853/2500000000 : ℝ)^4187 ≤ (1632145785347/12500000000000 : ℝ)^3163 := by
    have hnat : (537059853 : ℕ)^4187*12500000000000^3163 ≤ 1632145785347^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537059853 2500000000 1632145785347 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393909249/10000000000 : ℝ)^4187 ≤ (44168152982819/100000000000000 : ℝ)^3163 := by
    have hnat : (5393909249 : ℕ)^4187*100000000000000^3163 ≤ 44168152982819^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393909249 10000000000 44168152982819 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658106461/1250000000 : ℝ)^4187 ≤ (42774680730353/100000000000000 : ℝ)^3163 := by
    have hnat : (658106461 : ℕ)^4187*100000000000000^3163 ≤ 42774680730353^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658106461 1250000000 42774680730353 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537059853/2500000000 : ℝ), (5393909249/10000000000 : ℝ), (658106461/1250000000 : ℝ)] ![(1632145785347/12500000000000 : ℝ), (44168152982819/100000000000000 : ℝ), (42774680730353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537059853/2500000000 : ℝ)|^4187 ≤ (1632145785347/12500000000000 : ℝ)^3163
        have hw : |(-537059853/2500000000 : ℝ)|=(537059853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393909249/10000000000 : ℝ)|^4187 ≤ (44168152982819/100000000000000 : ℝ)^3163
        have hw : |(5393909249/10000000000 : ℝ)|=(5393909249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658106461/1250000000 : ℝ)|^4187 ≤ (42774680730353/100000000000000 : ℝ)^3163
        have hw : |(658106461/1250000000 : ℝ)|=(658106461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672500443/5000000000 : ℝ)*x 0 + (-2213712047/10000000000 : ℝ)*x 1 + (5264851757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672500443/5000000000 : ℝ)^4187 ≤ (43638790342383/100000000000000 : ℝ)^3163 := by
    have hnat : (2672500443 : ℕ)^4187*100000000000000^3163 ≤ 43638790342383^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672500443 5000000000 43638790342383 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213712047/10000000000 : ℝ)^4187 ≤ (6793264084137/50000000000000 : ℝ)^3163 := by
    have hnat : (2213712047 : ℕ)^4187*50000000000000^3163 ≤ 6793264084137^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213712047 10000000000 6793264084137 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264851757/10000000000 : ℝ)^4187 ≤ (21387340736219/50000000000000 : ℝ)^3163 := by
    have hnat : (5264851757 : ℕ)^4187*50000000000000^3163 ≤ 21387340736219^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264851757 10000000000 21387340736219 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672500443/5000000000 : ℝ), (-2213712047/10000000000 : ℝ), (5264851757/10000000000 : ℝ)] ![(43638790342383/100000000000000 : ℝ), (6793264084137/50000000000000 : ℝ), (21387340736219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672500443/5000000000 : ℝ)|^4187 ≤ (43638790342383/100000000000000 : ℝ)^3163
        have hw : |(2672500443/5000000000 : ℝ)|=(2672500443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213712047/10000000000 : ℝ)|^4187 ≤ (6793264084137/50000000000000 : ℝ)^3163
        have hw : |(-2213712047/10000000000 : ℝ)|=(2213712047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264851757/10000000000 : ℝ)|^4187 ≤ (21387340736219/50000000000000 : ℝ)^3163
        have hw : |(5264851757/10000000000 : ℝ)|=(5264851757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345000881/10000000000 : ℝ)*x 0 + (1052970373/2000000000 : ℝ)*x 1 + (-2213711911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345000881/10000000000 : ℝ)^4187 ≤ (8727758057669/20000000000000 : ℝ)^3163 := by
    have hnat : (5345000881 : ℕ)^4187*20000000000000^3163 ≤ 8727758057669^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345000881 10000000000 8727758057669 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052970373/2000000000 : ℝ)^4187 ≤ (21387341316981/50000000000000 : ℝ)^3163 := by
    have hnat : (1052970373 : ℕ)^4187*50000000000000^3163 ≤ 21387341316981^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052970373 2000000000 21387341316981 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213711911/10000000000 : ℝ)^4187 ≤ (3396631765839/25000000000000 : ℝ)^3163 := by
    have hnat : (2213711911 : ℕ)^4187*25000000000000^3163 ≤ 3396631765839^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213711911 10000000000 3396631765839 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345000881/10000000000 : ℝ), (1052970373/2000000000 : ℝ), (-2213711911/10000000000 : ℝ)] ![(8727758057669/20000000000000 : ℝ), (21387341316981/50000000000000 : ℝ), (3396631765839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345000881/10000000000 : ℝ)|^4187 ≤ (8727758057669/20000000000000 : ℝ)^3163
        have hw : |(5345000881/10000000000 : ℝ)|=(5345000881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052970373/2000000000 : ℝ)|^4187 ≤ (21387341316981/50000000000000 : ℝ)^3163
        have hw : |(1052970373/2000000000 : ℝ)|=(1052970373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213711911/10000000000 : ℝ)|^4187 ≤ (3396631765839/25000000000000 : ℝ)^3163
        have hw : |(-2213711911/10000000000 : ℝ)|=(2213711911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359128843/10000000000 : ℝ)*x 0 + (2115830199/5000000000 : ℝ)*x 1 + (179615283/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359128843/10000000000 : ℝ)^4187 ≤ (16658189082849/50000000000000 : ℝ)^3163 := by
    have hnat : (4359128843 : ℕ)^4187*50000000000000^3163 ≤ 16658189082849^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359128843 10000000000 16658189082849 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115830199/5000000000 : ℝ)^4187 ≤ (32032894999641/100000000000000 : ℝ)^3163 := by
    have hnat : (2115830199 : ℕ)^4187*100000000000000^3163 ≤ 32032894999641^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115830199 5000000000 32032894999641 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179615283/400000000 : ℝ)^4187 ≤ (3465072681557/10000000000000 : ℝ)^3163 := by
    have hnat : (179615283 : ℕ)^4187*10000000000000^3163 ≤ 3465072681557^3163*400000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179615283 400000000 3465072681557 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359128843/10000000000 : ℝ), (2115830199/5000000000 : ℝ), (179615283/400000000 : ℝ)] ![(16658189082849/50000000000000 : ℝ), (32032894999641/100000000000000 : ℝ), (3465072681557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359128843/10000000000 : ℝ)|^4187 ≤ (16658189082849/50000000000000 : ℝ)^3163
        have hw : |(4359128843/10000000000 : ℝ)|=(4359128843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115830199/5000000000 : ℝ)|^4187 ≤ (32032894999641/100000000000000 : ℝ)^3163
        have hw : |(2115830199/5000000000 : ℝ)|=(2115830199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179615283/400000000 : ℝ)|^4187 ≤ (3465072681557/10000000000000 : ℝ)^3163
        have hw : |(179615283/400000000 : ℝ)|=(179615283/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107412219/500000000 : ℝ)*x 0 + (5265184551/10000000000 : ℝ)*x 1 + (539357529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107412219/500000000 : ℝ)^4187 ≤ (13057206254399/100000000000000 : ℝ)^3163 := by
    have hnat : (107412219 : ℕ)^4187*100000000000000^3163 ≤ 13057206254399^3163*500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107412219 500000000 13057206254399 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265184551/10000000000 : ℝ)^4187 ≤ (42778260659009/100000000000000 : ℝ)^3163 := by
    have hnat : (5265184551 : ℕ)^4187*100000000000000^3163 ≤ 42778260659009^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265184551 10000000000 42778260659009 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539357529/1000000000 : ℝ)^4187 ≤ (44164533069499/100000000000000 : ℝ)^3163 := by
    have hnat : (539357529 : ℕ)^4187*100000000000000^3163 ≤ 44164533069499^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539357529 1000000000 44164533069499 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107412219/500000000 : ℝ), (5265184551/10000000000 : ℝ), (539357529/1000000000 : ℝ)] ![(13057206254399/100000000000000 : ℝ), (42778260659009/100000000000000 : ℝ), (44164533069499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107412219/500000000 : ℝ)|^4187 ≤ (13057206254399/100000000000000 : ℝ)^3163
        have hw : |(-107412219/500000000 : ℝ)|=(107412219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265184551/10000000000 : ℝ)|^4187 ≤ (42778260659009/100000000000000 : ℝ)^3163
        have hw : |(5265184551/10000000000 : ℝ)|=(5265184551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539357529/1000000000 : ℝ)|^4187 ≤ (44164533069499/100000000000000 : ℝ)^3163
        have hw : |(539357529/1000000000 : ℝ)|=(539357529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312211201/10000000000 : ℝ)*x 0 + (-2084988379/10000000000 : ℝ)*x 1 + (21574301/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312211201/10000000000 : ℝ)^4187 ≤ (43284765402731/100000000000000 : ℝ)^3163 := by
    have hnat : (5312211201 : ℕ)^4187*100000000000000^3163 ≤ 43284765402731^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312211201 10000000000 43284765402731 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084988379/10000000000 : ℝ)^4187 ≤ (12550701949939/100000000000000 : ℝ)^3163 := by
    have hnat : (2084988379 : ℕ)^4187*100000000000000^3163 ≤ 12550701949939^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084988379 10000000000 12550701949939 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21574301/40000000 : ℝ)^4187 ≤ (44164532635927/100000000000000 : ℝ)^3163 := by
    have hnat : (21574301 : ℕ)^4187*100000000000000^3163 ≤ 44164532635927^3163*40000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21574301 40000000 44164532635927 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312211201/10000000000 : ℝ), (-2084988379/10000000000 : ℝ), (21574301/40000000 : ℝ)] ![(43284765402731/100000000000000 : ℝ), (12550701949939/100000000000000 : ℝ), (44164532635927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312211201/10000000000 : ℝ)|^4187 ≤ (43284765402731/100000000000000 : ℝ)^3163
        have hw : |(5312211201/10000000000 : ℝ)|=(5312211201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084988379/10000000000 : ℝ)|^4187 ≤ (12550701949939/100000000000000 : ℝ)^3163
        have hw : |(-2084988379/10000000000 : ℝ)|=(2084988379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21574301/40000000 : ℝ)|^4187 ≤ (44164532635927/100000000000000 : ℝ)^3163
        have hw : |(21574301/40000000 : ℝ)|=(21574301/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312210901/10000000000 : ℝ)*x 0 + (1078715109/2000000000 : ℝ)*x 1 + (-2084988383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312210901/10000000000 : ℝ)^4187 ≤ (10821190541727/25000000000000 : ℝ)^3163 := by
    have hnat : (5312210901 : ℕ)^4187*25000000000000^3163 ≤ 10821190541727^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312210901 10000000000 10821190541727 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078715109/2000000000 : ℝ)^4187 ≤ (11041133958379/25000000000000 : ℝ)^3163 := by
    have hnat : (1078715109 : ℕ)^4187*25000000000000^3163 ≤ 11041133958379^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078715109 2000000000 11041133958379 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084988383/10000000000 : ℝ)^4187 ≤ (12550701981813/100000000000000 : ℝ)^3163 := by
    have hnat : (2084988383 : ℕ)^4187*100000000000000^3163 ≤ 12550701981813^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084988383 10000000000 12550701981813 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312210901/10000000000 : ℝ), (1078715109/2000000000 : ℝ), (-2084988383/10000000000 : ℝ)] ![(10821190541727/25000000000000 : ℝ), (11041133958379/25000000000000 : ℝ), (12550701981813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312210901/10000000000 : ℝ)|^4187 ≤ (10821190541727/25000000000000 : ℝ)^3163
        have hw : |(5312210901/10000000000 : ℝ)|=(5312210901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078715109/2000000000 : ℝ)|^4187 ≤ (11041133958379/25000000000000 : ℝ)^3163
        have hw : |(1078715109/2000000000 : ℝ)|=(1078715109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084988383/10000000000 : ℝ)|^4187 ≤ (12550701981813/100000000000000 : ℝ)^3163
        have hw : |(-2084988383/10000000000 : ℝ)|=(2084988383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s5_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089784743/2500000000 : ℝ)*x 0 + (224485767/500000000 : ℝ)*x 1 + (2116164903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089784743/2500000000 : ℝ)^4187 ≤ (8329120160803/25000000000000 : ℝ)^3163 := by
    have hnat : (1089784743 : ℕ)^4187*25000000000000^3163 ≤ 8329120160803^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089784743 2500000000 8329120160803 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224485767/500000000 : ℝ)^4187 ≤ (17321958184131/50000000000000 : ℝ)^3163 := by
    have hnat : (224485767 : ℕ)^4187*50000000000000^3163 ≤ 17321958184131^3163*500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224485767 500000000 17321958184131 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116164903/5000000000 : ℝ)^4187 ≤ (32039602970549/100000000000000 : ℝ)^3163 := by
    have hnat : (2116164903 : ℕ)^4187*100000000000000^3163 ≤ 32039602970549^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116164903 5000000000 32039602970549 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089784743/2500000000 : ℝ), (224485767/500000000 : ℝ), (2116164903/5000000000 : ℝ)] ![(8329120160803/25000000000000 : ℝ), (17321958184131/50000000000000 : ℝ), (32039602970549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089784743/2500000000 : ℝ)|^4187 ≤ (8329120160803/25000000000000 : ℝ)^3163
        have hw : |(1089784743/2500000000 : ℝ)|=(1089784743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224485767/500000000 : ℝ)|^4187 ≤ (17321958184131/50000000000000 : ℝ)^3163
        have hw : |(224485767/500000000 : ℝ)|=(224485767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116164903/5000000000 : ℝ)|^4187 ≤ (32039602970549/100000000000000 : ℝ)^3163
        have hw : |(2116164903/5000000000 : ℝ)|=(2116164903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11247/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (13191021907461003/100000000000000000000 : ℝ) := by
    have hpowers : (11247/100000 : ℝ)^8373 ≤ (13191021907461003/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11247 : ℕ)^8373*100000000000000000000^2048 ≤ 13191021907461003^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11247 100000 13191021907461003 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11247/100000 : ℝ)) (X := (13191021907461003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8373/2048 : ℝ) ≤ (8638131627842783/25000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8373 ≤ (8638131627842783/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8373*25000000000000000000^2048 ≤ 8638131627842783^2048*50000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 8638131627842783 25000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (8638131627842783/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013191021907461003/50000000000000000000 : ℝ) ≤ (5000322614610491/5000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50013191021907461003/50000000000000000000 : ℝ)^2048 ≤ (5000322614610491/5000000000000000 : ℝ)^8373 := by
      have hnat : (50013191021907461003 : ℕ)^2048*5000000000000000^8373 ≤ 5000322614610491^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013191021907461003 50000000000000000000 5000322614610491 5000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000322614610491/5000000000000000 : ℝ)) (X := (50013191021907461003/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009548709683766427/20000000000000000000 : ℝ) ≤ (200023351525091/200000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (20009548709683766427/20000000000000000000 : ℝ)^2048 ≤ (200023351525091/200000000000000 : ℝ)^8373 := by
      have hnat : (20009548709683766427 : ℕ)^2048*200000000000000^8373 ≤ 200023351525091^8373*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009548709683766427 20000000000000000000 200023351525091 200000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200023351525091/200000000000000 : ℝ)) (X := (20009548709683766427/20000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508638131627842783/12500000000000000000 : ℝ) ≤ (5000844961644059/5000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (12508638131627842783/12500000000000000000 : ℝ)^2048 ≤ (5000844961644059/5000000000000000 : ℝ)^8373 := by
      have hnat : (12508638131627842783 : ℕ)^2048*5000000000000000^8373 ≤ 5000844961644059^8373*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508638131627842783 12500000000000000000 5000844961644059 5000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000844961644059/5000000000000000 : ℝ)) (X := (12508638131627842783/12500000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13191021907461003/100000000000000000000 : ℝ) ≤ ((14930088812754997321/14935000000000000000 : ℝ)+2*(16323344799/9334375000000 : ℝ)*(11247/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (14930088812754997321/14935000000000000000 : ℝ)+2*(16323344799/9334375000000 : ℝ)*(11247/100000 : ℝ)=(5000322614610491/5000000000000000 : ℝ) by norm_num, show 1+2*(13191021907461003/100000000000000000000 : ℝ)=(50013191021907461003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8638131627842783/25000000000000000000 : ℝ)+(13191021907461003/100000000000000000000 : ℝ) ≤ ((14930088812754997321/14935000000000000000 : ℝ)+(16323344799/9334375000000 : ℝ)*((7117/50000 : ℝ)+(11247/100000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (14930088812754997321/14935000000000000000 : ℝ)+(16323344799/9334375000000 : ℝ)*((7117/50000 : ℝ)+(11247/100000 : ℝ))=(200023351525091/200000000000000 : ℝ) by norm_num, show 1+(8638131627842783/25000000000000000000 : ℝ)+(13191021907461003/100000000000000000000 : ℝ)=(20009548709683766427/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8638131627842783/25000000000000000000 : ℝ) ≤ ((14930088812754997321/14935000000000000000 : ℝ)+2*(16323344799/9334375000000 : ℝ)*(7117/50000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (14930088812754997321/14935000000000000000 : ℝ)+2*(16323344799/9334375000000 : ℝ)*(7117/50000 : ℝ)=(5000844961644059/5000000000000000 : ℝ) by norm_num, show 1+2*(8638131627842783/25000000000000000000 : ℝ)=(12508638131627842783/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14930088812754997321/14935000000000000000 : ℝ)*(X 1 0+X 2 0)+(16323344799/9334375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14930088812754997321/14935000000000000000 : ℝ)) (alpha := (16323344799/9334375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14930088812754997321/14935000000000000000 : ℝ)*(X 0 1+X 2 1)+(16323344799/9334375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14930088812754997321/14935000000000000000 : ℝ)) (alpha := (16323344799/9334375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14930088812754997321/14935000000000000000 : ℝ)*(X 0 2+X 1 2)+(16323344799/9334375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14930088812754997321/14935000000000000000 : ℝ)) (alpha := (16323344799/9334375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-537059853/2500000000 : ℝ)*X 0 0+(5393909249/10000000000 : ℝ)*X 0 1+(658106461/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672500443/5000000000 : ℝ)*X 1 0+(-2213712047/10000000000 : ℝ)*X 1 1+(5264851757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345000881/10000000000 : ℝ)*X 2 0+(1052970373/2000000000 : ℝ)*X 2 1+(-2213711911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359128843/10000000000 : ℝ)*X 0 0+(2115830199/5000000000 : ℝ)*X 0 1+(179615283/400000000 : ℝ)*X 0 2+(4359128843/10000000000 : ℝ)*X 1 0+(2115830199/5000000000 : ℝ)*X 1 1+(179615283/400000000 : ℝ)*X 1 2+(4359128843/10000000000 : ℝ)*X 2 0+(2115830199/5000000000 : ℝ)*X 2 1+(179615283/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107412219/500000000 : ℝ)*X 0 0+(5265184551/10000000000 : ℝ)*X 0 1+(539357529/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312211201/10000000000 : ℝ)*X 1 0+(-2084988379/10000000000 : ℝ)*X 1 1+(21574301/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312210901/10000000000 : ℝ)*X 2 0+(1078715109/2000000000 : ℝ)*X 2 1+(-2084988383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089784743/2500000000 : ℝ)*X 0 0+(224485767/500000000 : ℝ)*X 0 1+(2116164903/5000000000 : ℝ)*X 0 2+(1089784743/2500000000 : ℝ)*X 1 0+(224485767/500000000 : ℝ)*X 1 1+(2116164903/5000000000 : ℝ)*X 1 2+(1089784743/2500000000 : ℝ)*X 2 0+(224485767/500000000 : ℝ)*X 2 1+(2116164903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (953647827873894224780185887/149350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1900389391/100000000000000 : ℝ)*(base19) + (1861797749/100000000000000 : ℝ)*(base23) + (123620049/100000000000000 : ℝ)*(upper3) + (2094117/12500000000000 : ℝ)*(upper4) + (157788383/50000000000000 : ℝ)*(upper5) + (1161380781951949/20000000000000 : ℝ)*(major0) + (1161380781951949/20000000000000 : ℝ)*(major1) + (1161380781951949/20000000000000 : ℝ)*(major2) + (3874267429272763/50000000000000 : ℝ)*(sp0) + (7748597414698793/100000000000000 : ℝ)*(sp1) + (1549719490658087/20000000000000 : ℝ)*(sp2) + (966296153600973/25000000000000 : ℝ)*(sp3) + (64456542659/100000000000000 : ℝ)*(sp4) + (1479823959/6250000000000 : ℝ)*(sp7) + (966302072896809/25000000000000 : ℝ)*(f.failure) + (968574914386023/12500000000000 : ℝ)*(f.sum) + (1949933353533/186687500000000000000000000 : ℝ)*base65 + (4697259905675971371/298700000000000000000000000000000 : ℝ)*base68 + (32472192242071371/298700000000000000000000000000000 : ℝ)*base70 + (1120796930145928629/298700000000000000000000000000000 : ℝ)*base71 + (3567855896197/2987000000000000000000000000 : ℝ)*base73 + (41430577751828629/298700000000000000000000000000000 : ℝ)*base75 + (2886485395525971371/298700000000000000000000000000000 : ℝ)*base78 + (1315432329026371371/298700000000000000000000000000000 : ℝ)*base80 + (16947198893459/2987000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2135317/2500000000000000000000 : ℝ)*base89 + (2135317/2500000000000000000000 : ℝ)*base91 + (2135317/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96831713145489338173096683/12875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110860503/6250000000000 : ℝ)*(base19) + (361463313/25000000000000 : ℝ)*(base23) + (28321379/20000000000000 : ℝ)*(upper3) + (56968207/100000000000000 : ℝ)*(lower4) + (119712131/100000000000000 : ℝ)*(upper5) + (5836968435634211/100000000000000 : ℝ)*(major0) + (5836968435634211/100000000000000 : ℝ)*(major1) + (5836968435634211/100000000000000 : ℝ)*(major2) + (25026944497/50000000000000 : ℝ)*(sp1) + (6351906559/12500000000000 : ℝ)*(sp2) + (7788716691716121/100000000000000 : ℝ)*(sp4) + (7788664864059079/100000000000000 : ℝ)*(sp5) + (7788664430610397/100000000000000 : ℝ)*(sp6) + (1942609964427651/50000000000000 : ℝ)*(sp7) + (1942609964427651/50000000000000 : ℝ)*(f.failure) + (7788716691716121/100000000000000 : ℝ)*(f.sum) + (510966486263/128750000000000000000000000 : ℝ)*base65 + (31944094094315561/51500000000000000000000000000000 : ℝ)*base68 + (301265945129184439/51500000000000000000000000000000 : ℝ)*base69 + (837960803971684439/51500000000000000000000000000000 : ℝ)*base71 + (4920684775303/515000000000000000000000000 : ℝ)*base74 + (823691878552184439/51500000000000000000000000000000 : ℝ)*base75 + (444522796222684439/51500000000000000000000000000000 : ℝ)*base77 + (257992924744684439/51500000000000000000000000000000 : ℝ)*base79 + (134450054523/515000000000000000000000000 : ℝ)*base82 + (21074663/5000000000000000000000 : ℝ)*base89 + (21074663/5000000000000000000000 : ℝ)*base91 + (21074663/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1181_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1181_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1181_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1181_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1181_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
