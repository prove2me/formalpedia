-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1130_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:44.061556+00:00
-- url     : https://prove2.me/submissions/204b37cb-51d4-4e2e-90b6-52fbca41e167

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
theorem support_rectangle_w1130_s3_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168700471/10000000000 : ℝ)*x 0 + (5430439541/10000000000 : ℝ)*x 1 + (1046186239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168700471/10000000000 : ℝ)^8323 ≤ (263379540667/2000000000000 : ℝ)^6275 := by
    have hnat : (2168700471 : ℕ)^8323*2000000000000^6275 ≤ 263379540667^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168700471 10000000000 263379540667 2000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430439541/10000000000 : ℝ)^8323 ≤ (44493019760689/100000000000000 : ℝ)^6275 := by
    have hnat : (5430439541 : ℕ)^8323*100000000000000^6275 ≤ 44493019760689^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430439541 10000000000 44493019760689 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046186239/2000000000 : ℝ)^8323 ≤ (330765649939/781250000000 : ℝ)^6275 := by
    have hnat : (1046186239 : ℕ)^8323*781250000000^6275 ≤ 330765649939^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046186239 2000000000 330765649939 781250000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168700471/10000000000 : ℝ), (5430439541/10000000000 : ℝ), (1046186239/2000000000 : ℝ)] ![(263379540667/2000000000000 : ℝ), (44493019760689/100000000000000 : ℝ), (330765649939/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168700471/10000000000 : ℝ)|^8323 ≤ (263379540667/2000000000000 : ℝ)^6275
        have hw : |(-2168700471/10000000000 : ℝ)|=(2168700471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430439541/10000000000 : ℝ)|^8323 ≤ (44493019760689/100000000000000 : ℝ)^6275
        have hw : |(5430439541/10000000000 : ℝ)|=(5430439541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046186239/2000000000 : ℝ)|^8323 ≤ (330765649939/781250000000 : ℝ)^6275
        have hw : |(1046186239/2000000000 : ℝ)|=(1046186239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669260913/1250000000 : ℝ)*x 0 + (-283838713/1250000000 : ℝ)*x 1 + (5230931083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669260913/1250000000 : ℝ)^8323 ≤ (43665184236541/100000000000000 : ℝ)^6275 := by
    have hnat : (669260913 : ℕ)^8323*100000000000000^6275 ≤ 43665184236541^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669260913 1250000000 43665184236541 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283838713/1250000000 : ℝ)^8323 ≤ (6998406880209/50000000000000 : ℝ)^6275 := by
    have hnat : (283838713 : ℕ)^8323*50000000000000^6275 ≤ 6998406880209^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283838713 1250000000 6998406880209 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230931083/10000000000 : ℝ)^8323 ≤ (42338001989829/100000000000000 : ℝ)^6275 := by
    have hnat : (5230931083 : ℕ)^8323*100000000000000^6275 ≤ 42338001989829^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230931083 10000000000 42338001989829 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669260913/1250000000 : ℝ), (-283838713/1250000000 : ℝ), (5230931083/10000000000 : ℝ)] ![(43665184236541/100000000000000 : ℝ), (6998406880209/50000000000000 : ℝ), (42338001989829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669260913/1250000000 : ℝ)|^8323 ≤ (43665184236541/100000000000000 : ℝ)^6275
        have hw : |(669260913/1250000000 : ℝ)|=(669260913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283838713/1250000000 : ℝ)|^8323 ≤ (6998406880209/50000000000000 : ℝ)^6275
        have hw : |(-283838713/1250000000 : ℝ)|=(283838713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230931083/10000000000 : ℝ)|^8323 ≤ (42338001989829/100000000000000 : ℝ)^6275
        have hw : |(5230931083/10000000000 : ℝ)|=(5230931083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338521849/2500000000 : ℝ)*x 0 + (2615465591/5000000000 : ℝ)*x 1 + (-567677363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338521849/2500000000 : ℝ)^8323 ≤ (21832592615863/50000000000000 : ℝ)^6275 := by
    have hnat : (1338521849 : ℕ)^8323*50000000000000^6275 ≤ 21832592615863^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338521849 2500000000 21832592615863 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615465591/5000000000 : ℝ)^8323 ≤ (5292250381579/12500000000000 : ℝ)^6275 := by
    have hnat : (2615465591 : ℕ)^8323*12500000000000^6275 ≤ 5292250381579^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615465591 5000000000 5292250381579 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567677363/2500000000 : ℝ)^8323 ≤ (139968117001/1000000000000 : ℝ)^6275 := by
    have hnat : (567677363 : ℕ)^8323*1000000000000^6275 ≤ 139968117001^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567677363 2500000000 139968117001 1000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338521849/2500000000 : ℝ), (2615465591/5000000000 : ℝ), (-567677363/2500000000 : ℝ)] ![(21832592615863/50000000000000 : ℝ), (5292250381579/12500000000000 : ℝ), (139968117001/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338521849/2500000000 : ℝ)|^8323 ≤ (21832592615863/50000000000000 : ℝ)^6275
        have hw : |(1338521849/2500000000 : ℝ)|=(1338521849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615465591/5000000000 : ℝ)|^8323 ≤ (5292250381579/12500000000000 : ℝ)^6275
        have hw : |(2615465591/5000000000 : ℝ)|=(2615465591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567677363/2500000000 : ℝ)|^8323 ≤ (139968117001/1000000000000 : ℝ)^6275
        have hw : |(-567677363/2500000000 : ℝ)|=(567677363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364029763/10000000000 : ℝ)*x 0 + (208525707/500000000 : ℝ)*x 1 + (35675753/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364029763/10000000000 : ℝ)^8323 ≤ (3329325311321/10000000000000 : ℝ)^6275 := by
    have hnat : (4364029763 : ℕ)^8323*10000000000000^6275 ≤ 3329325311321^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364029763 10000000000 3329325311321 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208525707/500000000 : ℝ)^8323 ≤ (6269879046569/20000000000000 : ℝ)^6275 := by
    have hnat : (208525707 : ℕ)^8323*20000000000000^6275 ≤ 6269879046569^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208525707 500000000 6269879046569 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35675753/78125000 : ℝ)^8323 ≤ (17678675821557/50000000000000 : ℝ)^6275 := by
    have hnat : (35675753 : ℕ)^8323*50000000000000^6275 ≤ 17678675821557^6275*78125000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35675753 78125000 17678675821557 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364029763/10000000000 : ℝ), (208525707/500000000 : ℝ), (35675753/78125000 : ℝ)] ![(3329325311321/10000000000000 : ℝ), (6269879046569/20000000000000 : ℝ), (17678675821557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364029763/10000000000 : ℝ)|^8323 ≤ (3329325311321/10000000000000 : ℝ)^6275
        have hw : |(4364029763/10000000000 : ℝ)|=(4364029763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208525707/500000000 : ℝ)|^8323 ≤ (6269879046569/20000000000000 : ℝ)^6275
        have hw : |(208525707/500000000 : ℝ)|=(208525707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35675753/78125000 : ℝ)|^8323 ≤ (17678675821557/50000000000000 : ℝ)^6275
        have hw : |(35675753/78125000 : ℝ)|=(35675753/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168719143/10000000000 : ℝ)*x 0 + (523171171/1000000000 : ℝ)*x 1 + (5429654627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168719143/10000000000 : ℝ)^8323 ≤ (526765096811/4000000000000 : ℝ)^6275 := by
    have hnat : (2168719143 : ℕ)^8323*4000000000000^6275 ≤ 526765096811^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168719143 10000000000 526765096811 4000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523171171/1000000000 : ℝ)^8323 ≤ (42346382523387/100000000000000 : ℝ)^6275 := by
    have hnat : (523171171 : ℕ)^8323*100000000000000^6275 ≤ 42346382523387^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523171171 1000000000 42346382523387 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429654627/10000000000 : ℝ)^8323 ≤ (5560561254791/12500000000000 : ℝ)^6275 := by
    have hnat : (5429654627 : ℕ)^8323*12500000000000^6275 ≤ 5560561254791^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429654627 10000000000 5560561254791 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168719143/10000000000 : ℝ), (523171171/1000000000 : ℝ), (5429654627/10000000000 : ℝ)] ![(526765096811/4000000000000 : ℝ), (42346382523387/100000000000000 : ℝ), (5560561254791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168719143/10000000000 : ℝ)|^8323 ≤ (526765096811/4000000000000 : ℝ)^6275
        have hw : |(-2168719143/10000000000 : ℝ)|=(2168719143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523171171/1000000000 : ℝ)|^8323 ≤ (42346382523387/100000000000000 : ℝ)^6275
        have hw : |(523171171/1000000000 : ℝ)|=(523171171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429654627/10000000000 : ℝ)|^8323 ≤ (5560561254791/12500000000000 : ℝ)^6275
        have hw : |(5429654627/10000000000 : ℝ)|=(5429654627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303587109/10000000000 : ℝ)*x 0 + (-2071986759/10000000000 : ℝ)*x 1 + (2714827153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303587109/10000000000 : ℝ)^8323 ≤ (43119754684003/100000000000000 : ℝ)^6275 := by
    have hnat : (5303587109 : ℕ)^8323*100000000000000^6275 ≤ 43119754684003^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303587109 10000000000 43119754684003 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071986759/10000000000 : ℝ)^8323 ≤ (1239575875283/10000000000000 : ℝ)^6275 := by
    have hnat : (2071986759 : ℕ)^8323*10000000000000^6275 ≤ 1239575875283^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071986759 10000000000 1239575875283 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714827153/5000000000 : ℝ)^8323 ≤ (22242243275039/50000000000000 : ℝ)^6275 := by
    have hnat : (2714827153 : ℕ)^8323*50000000000000^6275 ≤ 22242243275039^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714827153 5000000000 22242243275039 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303587109/10000000000 : ℝ), (-2071986759/10000000000 : ℝ), (2714827153/5000000000 : ℝ)] ![(43119754684003/100000000000000 : ℝ), (1239575875283/10000000000000 : ℝ), (22242243275039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303587109/10000000000 : ℝ)|^8323 ≤ (43119754684003/100000000000000 : ℝ)^6275
        have hw : |(5303587109/10000000000 : ℝ)|=(5303587109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071986759/10000000000 : ℝ)|^8323 ≤ (1239575875283/10000000000000 : ℝ)^6275
        have hw : |(-2071986759/10000000000 : ℝ)|=(2071986759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714827153/5000000000 : ℝ)|^8323 ≤ (22242243275039/50000000000000 : ℝ)^6275
        have hw : |(2714827153/5000000000 : ℝ)|=(2714827153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303587929/10000000000 : ℝ)*x 0 + (5429653791/10000000000 : ℝ)*x 1 + (-41439727/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303587929/10000000000 : ℝ)^8323 ≤ (21559881763369/50000000000000 : ℝ)^6275 := by
    have hnat : (5303587929 : ℕ)^8323*50000000000000^6275 ≤ 21559881763369^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303587929 10000000000 21559881763369 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429653791/10000000000 : ℝ)^8323 ≤ (8896896190733/20000000000000 : ℝ)^6275 := by
    have hnat : (5429653791 : ℕ)^8323*20000000000000^6275 ≤ 8896896190733^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429653791 10000000000 8896896190733 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41439727/200000000 : ℝ)^8323 ≤ (99166044059/800000000000 : ℝ)^6275 := by
    have hnat : (41439727 : ℕ)^8323*800000000000^6275 ≤ 99166044059^6275*200000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41439727 200000000 99166044059 800000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303587929/10000000000 : ℝ), (5429653791/10000000000 : ℝ), (-41439727/200000000 : ℝ)] ![(21559881763369/50000000000000 : ℝ), (8896896190733/20000000000000 : ℝ), (99166044059/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303587929/10000000000 : ℝ)|^8323 ≤ (21559881763369/50000000000000 : ℝ)^6275
        have hw : |(5303587929/10000000000 : ℝ)|=(5303587929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429653791/10000000000 : ℝ)|^8323 ≤ (8896896190733/20000000000000 : ℝ)^6275
        have hw : |(5429653791/10000000000 : ℝ)|=(5429653791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41439727/200000000 : ℝ)|^8323 ≤ (99166044059/800000000000 : ℝ)^6275
        have hw : |(-41439727/200000000 : ℝ)|=(41439727/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s3_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136377081/312500000 : ℝ)*x 0 + (4564947279/10000000000 : ℝ)*x 1 + (1043018057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136377081/312500000 : ℝ)^8323 ≤ (33293625783883/100000000000000 : ℝ)^6275 := by
    have hnat : (136377081 : ℕ)^8323*100000000000000^6275 ≤ 33293625783883^6275*312500000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136377081 312500000 33293625783883 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4564947279/10000000000 : ℝ)^8323 ≤ (17670721748239/50000000000000 : ℝ)^6275 := by
    have hnat : (4564947279 : ℕ)^8323*50000000000000^6275 ≤ 17670721748239^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564947279 10000000000 17670721748239 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043018057/2500000000 : ℝ)^8323 ≤ (7841232673869/25000000000000 : ℝ)^6275 := by
    have hnat : (1043018057 : ℕ)^8323*25000000000000^6275 ≤ 7841232673869^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043018057 2500000000 7841232673869 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136377081/312500000 : ℝ), (4564947279/10000000000 : ℝ), (1043018057/2500000000 : ℝ)] ![(33293625783883/100000000000000 : ℝ), (17670721748239/50000000000000 : ℝ), (7841232673869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136377081/312500000 : ℝ)|^8323 ≤ (33293625783883/100000000000000 : ℝ)^6275
        have hw : |(136377081/312500000 : ℝ)|=(136377081/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4564947279/10000000000 : ℝ)|^8323 ≤ (17670721748239/50000000000000 : ℝ)^6275
        have hw : |(4564947279/10000000000 : ℝ)|=(4564947279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043018057/2500000000 : ℝ)|^8323 ≤ (7841232673869/25000000000000 : ℝ)^6275
        have hw : |(1043018057/2500000000 : ℝ)|=(1043018057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10599/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (741/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16539/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1803/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16539/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1803/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16539/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1803/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16539/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1803/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16539/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1803/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16539/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1803/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1803/20000 : ℝ) ^ (4161/1024 : ℝ) ≤ (5669277836444771/100000000000000000000 : ℝ) := by
    have hpowers : (1803/20000 : ℝ)^4161 ≤ (5669277836444771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1803 : ℕ)^4161*100000000000000000000^1024 ≤ 5669277836444771^1024*20000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1803 20000 5669277836444771 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1803/20000 : ℝ)) (X := (5669277836444771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16539/100000 : ℝ) ^ (4161/1024 : ℝ) ≤ (66746829624532783/100000000000000000000 : ℝ) := by
    have hpowers : (16539/100000 : ℝ)^4161 ≤ (66746829624532783/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16539 : ℕ)^4161*100000000000000000000^1024 ≤ 66746829624532783^1024*100000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16539 100000 66746829624532783 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16539/100000 : ℝ)) (X := (66746829624532783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005669277836444771/50000000000000000000 : ℝ) ≤ (5000139511953737/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50005669277836444771/50000000000000000000 : ℝ)^1024 ≤ (5000139511953737/5000000000000000 : ℝ)^4161 := by
      have hnat : (50005669277836444771 : ℕ)^1024*5000000000000000^4161 ≤ 5000139511953737^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005669277836444771 50000000000000000000 5000139511953737 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139511953737/5000000000000000 : ℝ)) (X := (50005669277836444771/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036208053730488777/50000000000000000000 : ℝ) ≤ (250044540891873/250000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50036208053730488777/50000000000000000000 : ℝ)^1024 ≤ (250044540891873/250000000000000 : ℝ)^4161 := by
      have hnat : (50036208053730488777 : ℕ)^1024*250000000000000^4161 ≤ 250044540891873^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036208053730488777 50000000000000000000 250044540891873 250000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250044540891873/250000000000000 : ℝ)) (X := (50036208053730488777/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50066746829624532783/50000000000000000000 : ℝ) ≤ (5001642123721183/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50066746829624532783/50000000000000000000 : ℝ)^1024 ≤ (5001642123721183/5000000000000000 : ℝ)^4161 := by
      have hnat : (50066746829624532783 : ℕ)^1024*5000000000000000^4161 ≤ 5001642123721183^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50066746829624532783 50000000000000000000 5001642123721183 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001642123721183/5000000000000000 : ℝ)) (X := (50066746829624532783/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5669277836444771/100000000000000000000 : ℝ) ≤ ((6267917273809398583/6270000000000000000 : ℝ)+2*(751305883723/376200000000000 : ℝ)*(1803/20000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (6267917273809398583/6270000000000000000 : ℝ)+2*(751305883723/376200000000000 : ℝ)*(1803/20000 : ℝ)=(5000139511953737/5000000000000000 : ℝ) by norm_num, show 1+2*(5669277836444771/100000000000000000000 : ℝ)=(50005669277836444771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(66746829624532783/100000000000000000000 : ℝ)+(5669277836444771/100000000000000000000 : ℝ) ≤ ((6267917273809398583/6270000000000000000 : ℝ)+(751305883723/376200000000000 : ℝ)*((16539/100000 : ℝ)+(1803/20000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (6267917273809398583/6270000000000000000 : ℝ)+(751305883723/376200000000000 : ℝ)*((16539/100000 : ℝ)+(1803/20000 : ℝ))=(250044540891873/250000000000000 : ℝ) by norm_num, show 1+(66746829624532783/100000000000000000000 : ℝ)+(5669277836444771/100000000000000000000 : ℝ)=(50036208053730488777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(66746829624532783/100000000000000000000 : ℝ) ≤ ((6267917273809398583/6270000000000000000 : ℝ)+2*(751305883723/376200000000000 : ℝ)*(16539/100000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (6267917273809398583/6270000000000000000 : ℝ)+2*(751305883723/376200000000000 : ℝ)*(16539/100000 : ℝ)=(5001642123721183/5000000000000000 : ℝ) by norm_num, show 1+2*(66746829624532783/100000000000000000000 : ℝ)=(50066746829624532783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6267917273809398583/6270000000000000000 : ℝ)*(X 1 0+X 2 0)+(751305883723/376200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (1803/20000 : ℝ)) (hi := (16539/100000 : ℝ)) (c := (6267917273809398583/6270000000000000000 : ℝ)) (alpha := (751305883723/376200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6267917273809398583/6270000000000000000 : ℝ)*(X 0 1+X 2 1)+(751305883723/376200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (1803/20000 : ℝ)) (hi := (16539/100000 : ℝ)) (c := (6267917273809398583/6270000000000000000 : ℝ)) (alpha := (751305883723/376200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6267917273809398583/6270000000000000000 : ℝ)*(X 0 2+X 1 2)+(751305883723/376200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (1803/20000 : ℝ)) (hi := (16539/100000 : ℝ)) (c := (6267917273809398583/6270000000000000000 : ℝ)) (alpha := (751305883723/376200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2168700471/10000000000 : ℝ)*X 0 0+(5430439541/10000000000 : ℝ)*X 0 1+(1046186239/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669260913/1250000000 : ℝ)*X 1 0+(-283838713/1250000000 : ℝ)*X 1 1+(5230931083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338521849/2500000000 : ℝ)*X 2 0+(2615465591/5000000000 : ℝ)*X 2 1+(-567677363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364029763/10000000000 : ℝ)*X 0 0+(208525707/500000000 : ℝ)*X 0 1+(35675753/78125000 : ℝ)*X 0 2+(4364029763/10000000000 : ℝ)*X 1 0+(208525707/500000000 : ℝ)*X 1 1+(35675753/78125000 : ℝ)*X 1 2+(4364029763/10000000000 : ℝ)*X 2 0+(208525707/500000000 : ℝ)*X 2 1+(35675753/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2168719143/10000000000 : ℝ)*X 0 0+(523171171/1000000000 : ℝ)*X 0 1+(5429654627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303587109/10000000000 : ℝ)*X 1 0+(-2071986759/10000000000 : ℝ)*X 1 1+(2714827153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303587929/10000000000 : ℝ)*X 2 0+(5429653791/10000000000 : ℝ)*X 2 1+(-41439727/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136377081/312500000 : ℝ)*X 0 0+(4564947279/10000000000 : ℝ)*X 0 1+(1043018057/2500000000 : ℝ)*X 0 2+(136377081/312500000 : ℝ)*X 1 0+(4564947279/10000000000 : ℝ)*X 1 1+(1043018057/2500000000 : ℝ)*X 1 2+(136377081/312500000 : ℝ)*X 2 0+(4564947279/10000000000 : ℝ)*X 2 1+(1043018057/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186360882240174663783/55000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086234533/100000000000000 : ℝ)*(base19) + (1030569493/100000000000000 : ℝ)*(base23) + (37958627/50000000000000 : ℝ)*(lower2) + (573681/25000000000000 : ℝ)*(upper3) + (174340103/100000000000000 : ℝ)*(upper5) + (942217858290807/25000000000000 : ℝ)*(major0) + (942217858290807/25000000000000 : ℝ)*(major1) + (942217858290807/25000000000000 : ℝ)*(major2) + (1253084279797127/25000000000000 : ℝ)*(sp0) + (5012359160552537/100000000000000 : ℝ)*(sp1) + (5012359216217577/100000000000000 : ℝ)*(sp2) + (2525374839578309/100000000000000 : ℝ)*(sp3) + (11563799281/50000000000000 : ℝ)*(sp4) + (7667015083/100000000000000 : ℝ)*(sp7) + (157836406662087/6250000000000 : ℝ)*(f.failure) + (501236024678707/10000000000000 : ℝ)*(f.sum) + (64071472813/55000000000000000000000000 : ℝ)*base66 + (31703371324152167/2750000000000000000000000000000 : ℝ)*base68 + (697255383902167/2750000000000000000000000000000 : ℝ)*base70 + (8832305489347833/2750000000000000000000000000000 : ℝ)*base71 + (24874133313/55000000000000000000000000 : ℝ)*base74 + (981204260652167/2750000000000000000000000000000 : ℝ)*base76 + (31292465068347833/2750000000000000000000000000000 : ℝ)*base77 + (26169745719347833/2750000000000000000000000000000 : ℝ)*base79 + (96186457849/27500000000000000000000000 : ℝ)*base82 + (3921549/625000000000000000000 : ℝ)*base89 + (3921549/625000000000000000000 : ℝ)*base91 + (3921549/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (244124069287395885253/130625000000000000000000000 : ℝ) := by norm_num
    linear_combination (183949057/50000000000000 : ℝ)*(base19) + (1285871669/100000000000000 : ℝ)*(base23) + (6549781/100000000000000 : ℝ)*(lower4) + (10730121/25000000000000 : ℝ)*(upper5) + (1899328640591617/50000000000000 : ℝ)*(major0) + (1899328640591617/50000000000000 : ℝ)*(major1) + (1899328640591617/50000000000000 : ℝ)*(major2) + (2401368841/100000000000000 : ℝ)*(sp0) + (337747579/12500000000000 : ℝ)*(sp1) + (15780130131/100000000000000 : ℝ)*(sp2) + (2525985593941589/50000000000000 : ℝ)*(sp4) + (5051970519373273/100000000000000 : ℝ)*(sp5) + (5051956523250219/100000000000000 : ℝ)*(sp6) + (159083806926127/6250000000000 : ℝ)*(sp7) + (159083806926127/6250000000000 : ℝ)*(f.failure) + (5051973589252019/100000000000000 : ℝ)*(f.sum) + (11009238788899/2351250000000000000000000000 : ℝ)*base65 + (586374106444486133/940500000000000000000000000000000 : ℝ)*base67 + (3189623926879513867/940500000000000000000000000000000 : ℝ)*base70 + (1050593925925513867/940500000000000000000000000000000 : ℝ)*base72 + (19380829273463/4702500000000000000000000000 : ℝ)*base73 + (281116760496013867/940500000000000000000000000000000 : ℝ)*base76 + (759961267873486133/940500000000000000000000000000000 : ℝ)*base77 + (253231409689486133/940500000000000000000000000000000 : ℝ)*base79 + (26450357038321/9405000000000000000000000000 : ℝ)*base81 + (2465371/625000000000000000000 : ℝ)*base90 + (2465371/625000000000000000000 : ℝ)*base92 + (2465371/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1130_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (741/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1130_s4_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542950439/2500000000 : ℝ)*x 0 + (5402473023/10000000000 : ℝ)*x 1 + (5256869419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542950439/2500000000 : ℝ)^8323 ≤ (164924512659/1250000000000 : ℝ)^6275 := by
    have hnat : (542950439 : ℕ)^8323*1250000000000^6275 ≤ 164924512659^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542950439 2500000000 164924512659 1250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402473023/10000000000 : ℝ)^8323 ≤ (44189353948189/100000000000000 : ℝ)^6275 := by
    have hnat : (5402473023 : ℕ)^8323*100000000000000^6275 ≤ 44189353948189^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402473023 10000000000 44189353948189 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256869419/10000000000 : ℝ)^8323 ≤ (21308342512053/50000000000000 : ℝ)^6275 := by
    have hnat : (5256869419 : ℕ)^8323*50000000000000^6275 ≤ 21308342512053^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256869419 10000000000 21308342512053 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542950439/2500000000 : ℝ), (5402473023/10000000000 : ℝ), (5256869419/10000000000 : ℝ)] ![(164924512659/1250000000000 : ℝ), (44189353948189/100000000000000 : ℝ), (21308342512053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542950439/2500000000 : ℝ)|^8323 ≤ (164924512659/1250000000000 : ℝ)^6275
        have hw : |(-542950439/2500000000 : ℝ)|=(542950439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402473023/10000000000 : ℝ)|^8323 ≤ (44189353948189/100000000000000 : ℝ)^6275
        have hw : |(5402473023/10000000000 : ℝ)|=(5402473023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256869419/10000000000 : ℝ)|^8323 ≤ (21308342512053/50000000000000 : ℝ)^6275
        have hw : |(5256869419/10000000000 : ℝ)|=(5256869419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069422299/2000000000 : ℝ)*x 0 + (-14036289/62500000 : ℝ)*x 1 + (5256869597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069422299/2000000000 : ℝ)^8323 ≤ (1743589654539/4000000000000 : ℝ)^6275 := by
    have hnat : (1069422299 : ℕ)^8323*4000000000000^6275 ≤ 1743589654539^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069422299 2000000000 1743589654539 4000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14036289/62500000 : ℝ)^8323 ≤ (1724196461511/12500000000000 : ℝ)^6275 := by
    have hnat : (14036289 : ℕ)^8323*12500000000000^6275 ≤ 1724196461511^6275*62500000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14036289 62500000 1724196461511 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256869597/10000000000 : ℝ)^8323 ≤ (42616686938091/100000000000000 : ℝ)^6275 := by
    have hnat : (5256869597 : ℕ)^8323*100000000000000^6275 ≤ 42616686938091^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256869597 10000000000 42616686938091 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069422299/2000000000 : ℝ), (-14036289/62500000 : ℝ), (5256869597/10000000000 : ℝ)] ![(1743589654539/4000000000000 : ℝ), (1724196461511/12500000000000 : ℝ), (42616686938091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069422299/2000000000 : ℝ)|^8323 ≤ (1743589654539/4000000000000 : ℝ)^6275
        have hw : |(1069422299/2000000000 : ℝ)|=(1069422299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14036289/62500000 : ℝ)|^8323 ≤ (1724196461511/12500000000000 : ℝ)^6275
        have hw : |(-14036289/62500000 : ℝ)|=(14036289/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256869597/10000000000 : ℝ)|^8323 ≤ (42616686938091/100000000000000 : ℝ)^6275
        have hw : |(5256869597/10000000000 : ℝ)|=(5256869597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347112091/10000000000 : ℝ)*x 0 + (5133661/9765625 : ℝ)*x 1 + (-140362901/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347112091/10000000000 : ℝ)^8323 ≤ (43589747807801/100000000000000 : ℝ)^6275 := by
    have hnat : (5347112091 : ℕ)^8323*100000000000000^6275 ≤ 43589747807801^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347112091 10000000000 43589747807801 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133661/9765625 : ℝ)^8323 ≤ (21308339528171/50000000000000 : ℝ)^6275 := by
    have hnat : (5133661 : ℕ)^8323*50000000000000^6275 ≤ 21308339528171^6275*9765625^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133661 9765625 21308339528171 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140362901/625000000 : ℝ)^8323 ≤ (1379357312587/10000000000000 : ℝ)^6275 := by
    have hnat : (140362901 : ℕ)^8323*10000000000000^6275 ≤ 1379357312587^6275*625000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140362901 625000000 1379357312587 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347112091/10000000000 : ℝ), (5133661/9765625 : ℝ), (-140362901/625000000 : ℝ)] ![(43589747807801/100000000000000 : ℝ), (21308339528171/50000000000000 : ℝ), (1379357312587/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347112091/10000000000 : ℝ)|^8323 ≤ (43589747807801/100000000000000 : ℝ)^6275
        have hw : |(5347112091/10000000000 : ℝ)|=(5347112091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133661/9765625 : ℝ)|^8323 ≤ (21308339528171/50000000000000 : ℝ)^6275
        have hw : |(5133661/9765625 : ℝ)|=(5133661/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140362901/625000000 : ℝ)|^8323 ≤ (1379357312587/10000000000000 : ℝ)^6275
        have hw : |(-140362901/625000000 : ℝ)|=(140362901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54573501/125000000 : ℝ)*x 0 + (2111883821/5000000000 : ℝ)*x 1 + (4512762177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54573501/125000000 : ℝ)^8323 ≤ (33311977641131/100000000000000 : ℝ)^6275 := by
    have hnat : (54573501 : ℕ)^8323*100000000000000^6275 ≤ 33311977641131^6275*125000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54573501 125000000 33311977641131 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111883821/5000000000 : ℝ)^8323 ≤ (31881448787013/100000000000000 : ℝ)^6275 := by
    have hnat : (2111883821 : ℕ)^8323*100000000000000^6275 ≤ 31881448787013^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111883821 5000000000 31881448787013 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512762177/10000000000 : ℝ)^8323 ≤ (34806573558757/100000000000000 : ℝ)^6275 := by
    have hnat : (4512762177 : ℕ)^8323*100000000000000^6275 ≤ 34806573558757^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512762177 10000000000 34806573558757 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54573501/125000000 : ℝ), (2111883821/5000000000 : ℝ), (4512762177/10000000000 : ℝ)] ![(33311977641131/100000000000000 : ℝ), (31881448787013/100000000000000 : ℝ), (34806573558757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54573501/125000000 : ℝ)|^8323 ≤ (33311977641131/100000000000000 : ℝ)^6275
        have hw : |(54573501/125000000 : ℝ)|=(54573501/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111883821/5000000000 : ℝ)|^8323 ≤ (31881448787013/100000000000000 : ℝ)^6275
        have hw : |(2111883821/5000000000 : ℝ)|=(2111883821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512762177/10000000000 : ℝ)|^8323 ≤ (34806573558757/100000000000000 : ℝ)^6275
        have hw : |(4512762177/10000000000 : ℝ)|=(4512762177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-271476221/1250000000 : ℝ)*x 0 + (2628642701/5000000000 : ℝ)*x 1 + (5402054771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271476221/1250000000 : ℝ)^8323 ≤ (13194025572551/100000000000000 : ℝ)^6275 := by
    have hnat : (271476221 : ℕ)^8323*100000000000000^6275 ≤ 13194025572551^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271476221 1250000000 13194025572551 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628642701/5000000000 : ℝ)^8323 ≤ (4262115803371/10000000000000 : ℝ)^6275 := by
    have hnat : (2628642701 : ℕ)^8323*10000000000000^6275 ≤ 4262115803371^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628642701 5000000000 4262115803371 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402054771/10000000000 : ℝ)^8323 ≤ (44184816373891/100000000000000 : ℝ)^6275 := by
    have hnat : (5402054771 : ℕ)^8323*100000000000000^6275 ≤ 44184816373891^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402054771 10000000000 44184816373891 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271476221/1250000000 : ℝ), (2628642701/5000000000 : ℝ), (5402054771/10000000000 : ℝ)] ![(13194025572551/100000000000000 : ℝ), (4262115803371/10000000000000 : ℝ), (44184816373891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271476221/1250000000 : ℝ)|^8323 ≤ (13194025572551/100000000000000 : ℝ)^6275
        have hw : |(-271476221/1250000000 : ℝ)|=(271476221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628642701/5000000000 : ℝ)|^8323 ≤ (4262115803371/10000000000000 : ℝ)^6275
        have hw : |(2628642701/5000000000 : ℝ)|=(2628642701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402054771/10000000000 : ℝ)|^8323 ≤ (44184816373891/100000000000000 : ℝ)^6275
        have hw : |(5402054771/10000000000 : ℝ)|=(5402054771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212410299/400000000 : ℝ)*x 0 + (-2100620407/10000000000 : ℝ)*x 1 + (1350513733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212410299/400000000 : ℝ)^8323 ≤ (43191701487709/100000000000000 : ℝ)^6275 := by
    have hnat : (212410299 : ℕ)^8323*100000000000000^6275 ≤ 43191701487709^6275*400000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212410299 400000000 43191701487709 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100620407/10000000000 : ℝ)^8323 ≤ (1577935046863/12500000000000 : ℝ)^6275 := by
    have hnat : (2100620407 : ℕ)^8323*12500000000000^6275 ≤ 1577935046863^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100620407 10000000000 1577935046863 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350513733/2500000000 : ℝ)^8323 ≤ (22092409060271/50000000000000 : ℝ)^6275 := by
    have hnat : (1350513733 : ℕ)^8323*50000000000000^6275 ≤ 22092409060271^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350513733 2500000000 22092409060271 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212410299/400000000 : ℝ), (-2100620407/10000000000 : ℝ), (1350513733/2500000000 : ℝ)] ![(43191701487709/100000000000000 : ℝ), (1577935046863/12500000000000 : ℝ), (22092409060271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212410299/400000000 : ℝ)|^8323 ≤ (43191701487709/100000000000000 : ℝ)^6275
        have hw : |(212410299/400000000 : ℝ)|=(212410299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100620407/10000000000 : ℝ)|^8323 ≤ (1577935046863/12500000000000 : ℝ)^6275
        have hw : |(-2100620407/10000000000 : ℝ)|=(2100620407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350513733/2500000000 : ℝ)|^8323 ≤ (22092409060271/50000000000000 : ℝ)^6275
        have hw : |(1350513733/2500000000 : ℝ)|=(1350513733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310257619/10000000000 : ℝ)*x 0 + (1350513711/2500000000 : ℝ)*x 1 + (-2100620331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310257619/10000000000 : ℝ)^8323 ≤ (674870360019/1562500000000 : ℝ)^6275 := by
    have hnat : (5310257619 : ℕ)^8323*1562500000000^6275 ≤ 674870360019^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310257619 10000000000 674870360019 1562500000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350513711/2500000000 : ℝ)^8323 ≤ (44184817165851/100000000000000 : ℝ)^6275 := by
    have hnat : (1350513711 : ℕ)^8323*100000000000000^6275 ≤ 44184817165851^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350513711 2500000000 44184817165851 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100620331/10000000000 : ℝ)^8323 ≤ (12623479769129/100000000000000 : ℝ)^6275 := by
    have hnat : (2100620331 : ℕ)^8323*100000000000000^6275 ≤ 12623479769129^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100620331 10000000000 12623479769129 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310257619/10000000000 : ℝ), (1350513711/2500000000 : ℝ), (-2100620331/10000000000 : ℝ)] ![(674870360019/1562500000000 : ℝ), (44184817165851/100000000000000 : ℝ), (12623479769129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310257619/10000000000 : ℝ)|^8323 ≤ (674870360019/1562500000000 : ℝ)^6275
        have hw : |(5310257619/10000000000 : ℝ)|=(5310257619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350513711/2500000000 : ℝ)|^8323 ≤ (44184817165851/100000000000000 : ℝ)^6275
        have hw : |(1350513711/2500000000 : ℝ)|=(1350513711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100620331/10000000000 : ℝ)|^8323 ≤ (12623479769129/100000000000000 : ℝ)^6275
        have hw : |(-2100620331/10000000000 : ℝ)|=(2100620331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s4_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545736821/1250000000 : ℝ)*x 0 + (563991871/1250000000 : ℝ)*x 1 + (844919643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545736821/1250000000 : ℝ)^8323 ≤ (16656062132293/50000000000000 : ℝ)^6275 := by
    have hnat : (545736821 : ℕ)^8323*50000000000000^6275 ≤ 16656062132293^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545736821 1250000000 16656062132293 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563991871/1250000000 : ℝ)^8323 ≤ (17399055640761/50000000000000 : ℝ)^6275 := by
    have hnat : (563991871 : ℕ)^8323*50000000000000^6275 ≤ 17399055640761^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563991871 1250000000 17399055640761 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844919643/2000000000 : ℝ)^8323 ≤ (15944882215991/50000000000000 : ℝ)^6275 := by
    have hnat : (844919643 : ℕ)^8323*50000000000000^6275 ≤ 15944882215991^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844919643 2000000000 15944882215991 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545736821/1250000000 : ℝ), (563991871/1250000000 : ℝ), (844919643/2000000000 : ℝ)] ![(16656062132293/50000000000000 : ℝ), (17399055640761/50000000000000 : ℝ), (15944882215991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545736821/1250000000 : ℝ)|^8323 ≤ (16656062132293/50000000000000 : ℝ)^6275
        have hw : |(545736821/1250000000 : ℝ)|=(545736821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563991871/1250000000 : ℝ)|^8323 ≤ (17399055640761/50000000000000 : ℝ)^6275
        have hw : |(563991871/1250000000 : ℝ)|=(563991871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844919643/2000000000 : ℝ)|^8323 ≤ (15944882215991/50000000000000 : ℝ)^6275
        have hw : |(844919643/2000000000 : ℝ)|=(844919643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (741/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (697/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (741/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (741/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (741/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (741/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (741/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (741/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10599/100000 : ℝ) ^ (4161/1024 : ℝ) ≤ (5472134192059721/50000000000000000000 : ℝ) := by
    have hpowers : (10599/100000 : ℝ)^4161 ≤ (5472134192059721/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10599 : ℕ)^4161*50000000000000000000^1024 ≤ 5472134192059721^1024*100000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10599 100000 5472134192059721 50000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10599/100000 : ℝ)) (X := (5472134192059721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (741/5000 : ℝ) ^ (4161/1024 : ℝ) ≤ (42732776240587207/100000000000000000000 : ℝ) := by
    have hpowers : (741/5000 : ℝ)^4161 ≤ (42732776240587207/100000000000000000000 : ℝ)^1024 := by
      have hnat : (741 : ℕ)^4161*100000000000000000000^1024 ≤ 42732776240587207^1024*5000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        741 5000 42732776240587207 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (741/5000 : ℝ)) (X := (42732776240587207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005472134192059721/25000000000000000000 : ℝ) ≤ (625033663801569/625000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (25005472134192059721/25000000000000000000 : ℝ)^1024 ≤ (625033663801569/625000000000000 : ℝ)^4161 := by
      have hnat : (25005472134192059721 : ℕ)^1024*625000000000000^4161 ≤ 625033663801569^4161*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005472134192059721 25000000000000000000 625033663801569 625000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033663801569/625000000000000 : ℝ)) (X := (25005472134192059721/25000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053677044624706649/100000000000000000000 : ℝ) ≤ (125016508704539/125000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (100053677044624706649/100000000000000000000 : ℝ)^1024 ≤ (125016508704539/125000000000000 : ℝ)^4161 := by
      have hnat : (100053677044624706649 : ℕ)^1024*125000000000000^4161 ≤ 125016508704539^4161*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053677044624706649 100000000000000000000 125016508704539 125000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125016508704539/125000000000000 : ℝ)) (X := (100053677044624706649/100000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042732776240587207/50000000000000000000 : ℝ) ≤ (625131423243821/625000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50042732776240587207/50000000000000000000 : ℝ)^1024 ≤ (625131423243821/625000000000000 : ℝ)^4161 := by
      have hnat : (50042732776240587207 : ℕ)^1024*625000000000000^4161 ≤ 625131423243821^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042732776240587207 50000000000000000000 625131423243821 625000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625131423243821/625000000000000 : ℝ)) (X := (50042732776240587207/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5472134192059721/50000000000000000000 : ℝ) ≤ ((879076980859331267/879375000000000000 : ℝ)+2*(24439860563/13190625000000 : ℝ)*(10599/100000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (879076980859331267/879375000000000000 : ℝ)+2*(24439860563/13190625000000 : ℝ)*(10599/100000 : ℝ)=(625033663801569/625000000000000 : ℝ) by norm_num, show 1+2*(5472134192059721/50000000000000000000 : ℝ)=(25005472134192059721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42732776240587207/100000000000000000000 : ℝ)+(5472134192059721/50000000000000000000 : ℝ) ≤ ((879076980859331267/879375000000000000 : ℝ)+(24439860563/13190625000000 : ℝ)*((741/5000 : ℝ)+(10599/100000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (879076980859331267/879375000000000000 : ℝ)+(24439860563/13190625000000 : ℝ)*((741/5000 : ℝ)+(10599/100000 : ℝ))=(125016508704539/125000000000000 : ℝ) by norm_num, show 1+(42732776240587207/100000000000000000000 : ℝ)+(5472134192059721/50000000000000000000 : ℝ)=(100053677044624706649/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42732776240587207/100000000000000000000 : ℝ) ≤ ((879076980859331267/879375000000000000 : ℝ)+2*(24439860563/13190625000000 : ℝ)*(741/5000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (879076980859331267/879375000000000000 : ℝ)+2*(24439860563/13190625000000 : ℝ)*(741/5000 : ℝ)=(625131423243821/625000000000000 : ℝ) by norm_num, show 1+2*(42732776240587207/100000000000000000000 : ℝ)=(50042732776240587207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (879076980859331267/879375000000000000 : ℝ)*(X 1 0+X 2 0)+(24439860563/13190625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (10599/100000 : ℝ)) (hi := (741/5000 : ℝ)) (c := (879076980859331267/879375000000000000 : ℝ)) (alpha := (24439860563/13190625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (879076980859331267/879375000000000000 : ℝ)*(X 0 1+X 2 1)+(24439860563/13190625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (10599/100000 : ℝ)) (hi := (741/5000 : ℝ)) (c := (879076980859331267/879375000000000000 : ℝ)) (alpha := (24439860563/13190625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (879076980859331267/879375000000000000 : ℝ)*(X 0 2+X 1 2)+(24439860563/13190625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (10599/100000 : ℝ)) (hi := (741/5000 : ℝ)) (c := (879076980859331267/879375000000000000 : ℝ)) (alpha := (24439860563/13190625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-542950439/2500000000 : ℝ)*X 0 0+(5402473023/10000000000 : ℝ)*X 0 1+(5256869419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069422299/2000000000 : ℝ)*X 1 0+(-14036289/62500000 : ℝ)*X 1 1+(5256869597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347112091/10000000000 : ℝ)*X 2 0+(5133661/9765625 : ℝ)*X 2 1+(-140362901/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54573501/125000000 : ℝ)*X 0 0+(2111883821/5000000000 : ℝ)*X 0 1+(4512762177/10000000000 : ℝ)*X 0 2+(54573501/125000000 : ℝ)*X 1 0+(2111883821/5000000000 : ℝ)*X 1 1+(4512762177/10000000000 : ℝ)*X 1 2+(54573501/125000000 : ℝ)*X 2 0+(2111883821/5000000000 : ℝ)*X 2 1+(4512762177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-271476221/1250000000 : ℝ)*X 0 0+(2628642701/5000000000 : ℝ)*X 0 1+(5402054771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212410299/400000000 : ℝ)*X 1 0+(-2100620407/10000000000 : ℝ)*X 1 1+(1350513733/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310257619/10000000000 : ℝ)*X 2 0+(1350513711/2500000000 : ℝ)*X 2 1+(-2100620331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545736821/1250000000 : ℝ)*X 0 0+(563991871/1250000000 : ℝ)*X 0 1+(844919643/2000000000 : ℝ)*X 0 2+(545736821/1250000000 : ℝ)*X 1 0+(563991871/1250000000 : ℝ)*X 1 1+(844919643/2000000000 : ℝ)*X 1 2+(545736821/1250000000 : ℝ)*X 2 0+(563991871/1250000000 : ℝ)*X 2 1+(844919643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102071755877496281981014333/7328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321610719/50000000000000 : ℝ)*(base19) + (265232411/25000000000000 : ℝ)*(base23) + (92426921/25000000000000 : ℝ)*(lower2) + (367050189/100000000000000 : ℝ)*(upper3) + (183729709/100000000000000 : ℝ)*(lower4) + (5164136728503049/100000000000000 : ℝ)*(major0) + (5164136728503049/100000000000000 : ℝ)*(major1) + (5164136728503049/100000000000000 : ℝ)*(major2) + (686797023702307/10000000000000 : ℝ)*(sp0) + (6867973746291597/100000000000000 : ℝ)*(sp1) + (686797332858339/10000000000000 : ℝ)*(sp2) + (432534986115457/12500000000000 : ℝ)*(sp3) + (1038122491/25000000000000 : ℝ)*(sp4) + (14620529/78125000000 : ℝ)*(sp7) + (3460298603200777/100000000000000 : ℝ)*(f.failure) + (3433987194756517/50000000000000 : ℝ)*(f.sum) + (5799752742607/2638125000000000000000000000 : ℝ)*base66 + (2504126779379125751/263812500000000000000000000000000 : ℝ)*base68 + (987916416188875751/263812500000000000000000000000000 : ℝ)*base70 + (2559275913241938251/263812500000000000000000000000000 : ℝ)*base72 + (2456666725339/1319062500000000000000000000 : ℝ)*base73 + (441708947784813251/263812500000000000000000000000000 : ℝ)*base76 + (2197895255459125751/263812500000000000000000000000000 : ℝ)*base78 + (2000149062391999249/263812500000000000000000000000000 : ℝ)*base79 + (3429377127097/2638125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (65590179/10000000000000000000000 : ℝ)*base89 + (65590179/10000000000000000000000 : ℝ)*base91 + (65590179/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (382945287401166603394002689/43968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1862424533/100000000000000 : ℝ)*(base19) + (527726607/25000000000000 : ℝ)*(base23) + (69561463/25000000000000 : ℝ)*(upper3) + (521541/2000000000000 : ℝ)*(lower4) + (100362621/25000000000000 : ℝ)*(upper5) + (5193890449909489/100000000000000 : ℝ)*(major0) + (5193890449909489/100000000000000 : ℝ)*(major1) + (5193890449909489/100000000000000 : ℝ)*(major2) + (23738561293/50000000000000 : ℝ)*(sp1) + (12303588123/25000000000000 : ℝ)*(sp2) + (3453772564471327/50000000000000 : ℝ)*(sp4) + (3453747894697767/50000000000000 : ℝ)*(sp5) + (3453746901841867/50000000000000 : ℝ)*(sp6) + (1740117740280029/50000000000000 : ℝ)*(sp7) + (1740117740280029/50000000000000 : ℝ)*(f.failure) + (3453772564471327/50000000000000 : ℝ)*(f.sum) + (6664079287/164882812500000000000000000 : ℝ)*base66 + (337164570166272311/263812500000000000000000000000000 : ℝ)*base68 + (3144275630484522311/263812500000000000000000000000000 : ℝ)*base70 + (644175030755477689/263812500000000000000000000000000 : ℝ)*base71 + (50704821157303/10552500000000000000000000000 : ℝ)*base74 + (216692731635522311/263812500000000000000000000000000 : ℝ)*base76 + (2038588995929397311/263812500000000000000000000000000 : ℝ)*base78 + (1022794229058977689/263812500000000000000000000000000 : ℝ)*base79 + (17079177791551/5276250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (46490817/5000000000000000000000 : ℝ)*base90 + (46490817/5000000000000000000000 : ℝ)*base92 + (46490817/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1130_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (741/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1130_s5_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086232933/5000000000 : ℝ)*x 0 + (539523403/1000000000 : ℝ)*x 1 + (5263672521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086232933/5000000000 : ℝ)^8323 ≤ (13199312603173/100000000000000 : ℝ)^6275 := by
    have hnat : (1086232933 : ℕ)^8323*100000000000000^6275 ≤ 13199312603173^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086232933 5000000000 13199312603173 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539523403/1000000000 : ℝ)^8323 ≤ (5513854377469/12500000000000 : ℝ)^6275 := by
    have hnat : (539523403 : ℕ)^8323*12500000000000^6275 ≤ 5513854377469^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539523403 1000000000 5513854377469 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263672521/10000000000 : ℝ)^8323 ≤ (21344926185141/50000000000000 : ℝ)^6275 := by
    have hnat : (5263672521 : ℕ)^8323*50000000000000^6275 ≤ 21344926185141^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263672521 10000000000 21344926185141 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086232933/5000000000 : ℝ), (539523403/1000000000 : ℝ), (5263672521/10000000000 : ℝ)] ![(13199312603173/100000000000000 : ℝ), (5513854377469/12500000000000 : ℝ), (21344926185141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086232933/5000000000 : ℝ)|^8323 ≤ (13199312603173/100000000000000 : ℝ)^6275
        have hw : |(-1086232933/5000000000 : ℝ)|=(1086232933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539523403/1000000000 : ℝ)|^8323 ≤ (5513854377469/12500000000000 : ℝ)^6275
        have hw : |(539523403/1000000000 : ℝ)|=(539523403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263672521/10000000000 : ℝ)|^8323 ≤ (21344926185141/50000000000000 : ℝ)^6275
        have hw : |(5263672521/10000000000 : ℝ)|=(5263672521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345298677/10000000000 : ℝ)*x 0 + (-2239227913/10000000000 : ℝ)*x 1 + (526367247/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345298677/10000000000 : ℝ)^8323 ≤ (43570141123361/100000000000000 : ℝ)^6275 := by
    have hnat : (5345298677 : ℕ)^8323*100000000000000^6275 ≤ 43570141123361^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345298677 10000000000 43570141123361 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239227913/10000000000 : ℝ)^8323 ≤ (687000351961/5000000000000 : ℝ)^6275 := by
    have hnat : (2239227913 : ℕ)^8323*5000000000000^6275 ≤ 687000351961^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239227913 10000000000 687000351961 5000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526367247/1000000000 : ℝ)^8323 ≤ (42689851821661/100000000000000 : ℝ)^6275 := by
    have hnat : (526367247 : ℕ)^8323*100000000000000^6275 ≤ 42689851821661^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526367247 1000000000 42689851821661 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345298677/10000000000 : ℝ), (-2239227913/10000000000 : ℝ), (526367247/1000000000 : ℝ)] ![(43570141123361/100000000000000 : ℝ), (687000351961/5000000000000 : ℝ), (42689851821661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345298677/10000000000 : ℝ)|^8323 ≤ (43570141123361/100000000000000 : ℝ)^6275
        have hw : |(5345298677/10000000000 : ℝ)|=(5345298677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239227913/10000000000 : ℝ)|^8323 ≤ (687000351961/5000000000000 : ℝ)^6275
        have hw : |(-2239227913/10000000000 : ℝ)|=(2239227913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526367247/1000000000 : ℝ)|^8323 ≤ (42689851821661/100000000000000 : ℝ)^6275
        have hw : |(526367247/1000000000 : ℝ)|=(526367247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668162323/1250000000 : ℝ)*x 0 + (5263672553/10000000000 : ℝ)*x 1 + (-2239227927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668162323/1250000000 : ℝ)^8323 ≤ (21785070058949/50000000000000 : ℝ)^6275 := by
    have hnat : (668162323 : ℕ)^8323*50000000000000^6275 ≤ 21785070058949^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668162323 1250000000 21785070058949 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263672553/10000000000 : ℝ)^8323 ≤ (8537970542903/20000000000000 : ℝ)^6275 := by
    have hnat : (5263672553 : ℕ)^8323*20000000000000^6275 ≤ 8537970542903^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263672553 10000000000 8537970542903 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239227927/10000000000 : ℝ)^8323 ≤ (13740007153161/100000000000000 : ℝ)^6275 := by
    have hnat : (2239227927 : ℕ)^8323*100000000000000^6275 ≤ 13740007153161^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239227927 10000000000 13740007153161 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668162323/1250000000 : ℝ), (5263672553/10000000000 : ℝ), (-2239227927/10000000000 : ℝ)] ![(21785070058949/50000000000000 : ℝ), (8537970542903/20000000000000 : ℝ), (13740007153161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668162323/1250000000 : ℝ)|^8323 ≤ (21785070058949/50000000000000 : ℝ)^6275
        have hw : |(668162323/1250000000 : ℝ)|=(668162323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263672553/10000000000 : ℝ)|^8323 ≤ (8537970542903/20000000000000 : ℝ)^6275
        have hw : |(5263672553/10000000000 : ℝ)|=(5263672553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239227927/10000000000 : ℝ)|^8323 ≤ (13740007153161/100000000000000 : ℝ)^6275
        have hw : |(-2239227927/10000000000 : ℝ)|=(2239227927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873253373/2000000000 : ℝ)*x 0 + (4237653637/10000000000 : ℝ)*x 1 + (899755181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873253373/2000000000 : ℝ)^8323 ≤ (33315892090499/100000000000000 : ℝ)^6275 := by
    have hnat : (873253373 : ℕ)^8323*100000000000000^6275 ≤ 33315892090499^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873253373 2000000000 33315892090499 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237653637/10000000000 : ℝ)^8323 ≤ (16010272284497/50000000000000 : ℝ)^6275 := by
    have hnat : (4237653637 : ℕ)^8323*50000000000000^6275 ≤ 16010272284497^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237653637 10000000000 16010272284497 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899755181/2000000000 : ℝ)^8323 ≤ (1733178166489/5000000000000 : ℝ)^6275 := by
    have hnat : (899755181 : ℕ)^8323*5000000000000^6275 ≤ 1733178166489^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899755181 2000000000 1733178166489 5000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873253373/2000000000 : ℝ), (4237653637/10000000000 : ℝ), (899755181/2000000000 : ℝ)] ![(33315892090499/100000000000000 : ℝ), (16010272284497/50000000000000 : ℝ), (1733178166489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873253373/2000000000 : ℝ)|^8323 ≤ (33315892090499/100000000000000 : ℝ)^6275
        have hw : |(873253373/2000000000 : ℝ)|=(873253373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237653637/10000000000 : ℝ)|^8323 ≤ (16010272284497/50000000000000 : ℝ)^6275
        have hw : |(4237653637/10000000000 : ℝ)|=(4237653637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899755181/2000000000 : ℝ)|^8323 ≤ (1733178166489/5000000000000 : ℝ)^6275
        have hw : |(899755181/2000000000 : ℝ)|=(899755181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086235363/5000000000 : ℝ)*x 0 + (16450041/31250000 : ℝ)*x 1 + (1078978509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086235363/5000000000 : ℝ)^8323 ≤ (13199351768427/100000000000000 : ℝ)^6275 := by
    have hnat : (1086235363 : ℕ)^8323*100000000000000^6275 ≤ 13199351768427^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086235363 5000000000 13199351768427 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16450041/31250000 : ℝ)^8323 ≤ (5336689540427/12500000000000 : ℝ)^6275 := by
    have hnat : (16450041 : ℕ)^8323*12500000000000^6275 ≤ 5336689540427^6275*31250000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16450041 31250000 5336689540427 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078978509/2000000000 : ℝ)^8323 ≤ (5513391486919/12500000000000 : ℝ)^6275 := by
    have hnat : (1078978509 : ℕ)^8323*12500000000000^6275 ≤ 5513391486919^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078978509 2000000000 5513391486919 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086235363/5000000000 : ℝ), (16450041/31250000 : ℝ), (1078978509/2000000000 : ℝ)] ![(13199351768427/100000000000000 : ℝ), (5336689540427/12500000000000 : ℝ), (5513391486919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086235363/5000000000 : ℝ)|^8323 ≤ (13199351768427/100000000000000 : ℝ)^6275
        have hw : |(-1086235363/5000000000 : ℝ)|=(1086235363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16450041/31250000 : ℝ)|^8323 ≤ (5336689540427/12500000000000 : ℝ)^6275
        have hw : |(16450041/31250000 : ℝ)|=(16450041/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078978509/2000000000 : ℝ)|^8323 ≤ (5513391486919/12500000000000 : ℝ)^6275
        have hw : |(1078978509/2000000000 : ℝ)|=(1078978509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327999293/2500000000 : ℝ)*x 0 + (-1054003951/5000000000 : ℝ)*x 1 + (5394892499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327999293/2500000000 : ℝ)^8323 ≤ (4321047077271/10000000000000 : ℝ)^6275 := by
    have hnat : (1327999293 : ℕ)^8323*10000000000000^6275 ≤ 4321047077271^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327999293 2500000000 4321047077271 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054003951/5000000000 : ℝ)^8323 ≤ (12682397814723/100000000000000 : ℝ)^6275 := by
    have hnat : (1054003951 : ℕ)^8323*100000000000000^6275 ≤ 12682397814723^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054003951 5000000000 12682397814723 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394892499/10000000000 : ℝ)^8323 ≤ (1764285255861/4000000000000 : ℝ)^6275 := by
    have hnat : (5394892499 : ℕ)^8323*4000000000000^6275 ≤ 1764285255861^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394892499 10000000000 1764285255861 4000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327999293/2500000000 : ℝ), (-1054003951/5000000000 : ℝ), (5394892499/10000000000 : ℝ)] ![(4321047077271/10000000000000 : ℝ), (12682397814723/100000000000000 : ℝ), (1764285255861/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327999293/2500000000 : ℝ)|^8323 ≤ (4321047077271/10000000000000 : ℝ)^6275
        have hw : |(1327999293/2500000000 : ℝ)|=(1327999293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054003951/5000000000 : ℝ)|^8323 ≤ (12682397814723/100000000000000 : ℝ)^6275
        have hw : |(-1054003951/5000000000 : ℝ)|=(1054003951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394892499/10000000000 : ℝ)|^8323 ≤ (1764285255861/4000000000000 : ℝ)^6275
        have hw : |(5394892499/10000000000 : ℝ)|=(5394892499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132799921/250000000 : ℝ)*x 0 + (2697446367/5000000000 : ℝ)*x 1 + (-65875251/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132799921/250000000 : ℝ)^8323 ≤ (43210467190629/100000000000000 : ℝ)^6275 := by
    have hnat : (132799921 : ℕ)^8323*100000000000000^6275 ≤ 43210467190629^6275*250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132799921 250000000 43210467190629 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697446367/5000000000 : ℝ)^8323 ≤ (44107133944881/100000000000000 : ℝ)^6275 := by
    have hnat : (2697446367 : ℕ)^8323*100000000000000^6275 ≤ 44107133944881^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697446367 5000000000 44107133944881 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65875251/312500000 : ℝ)^8323 ≤ (2536479770421/20000000000000 : ℝ)^6275 := by
    have hnat : (65875251 : ℕ)^8323*20000000000000^6275 ≤ 2536479770421^6275*312500000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65875251 312500000 2536479770421 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132799921/250000000 : ℝ), (2697446367/5000000000 : ℝ), (-65875251/312500000 : ℝ)] ![(43210467190629/100000000000000 : ℝ), (44107133944881/100000000000000 : ℝ), (2536479770421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132799921/250000000 : ℝ)|^8323 ≤ (43210467190629/100000000000000 : ℝ)^6275
        have hw : |(132799921/250000000 : ℝ)|=(132799921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697446367/5000000000 : ℝ)|^8323 ≤ (44107133944881/100000000000000 : ℝ)^6275
        have hw : |(2697446367/5000000000 : ℝ)|=(2697446367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65875251/312500000 : ℝ)|^8323 ≤ (2536479770421/20000000000000 : ℝ)^6275
        have hw : |(-65875251/312500000 : ℝ)|=(65875251/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s5_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183138499/5000000000 : ℝ)*x 0 + (4498100699/10000000000 : ℝ)*x 1 + (4238331883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183138499/5000000000 : ℝ)^8323 ≤ (2082249665177/6250000000000 : ℝ)^6275 := by
    have hnat : (2183138499 : ℕ)^8323*6250000000000^6275 ≤ 2082249665177^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183138499 5000000000 2082249665177 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498100699/10000000000 : ℝ)^8323 ≤ (34656662987009/100000000000000 : ℝ)^6275 := by
    have hnat : (4498100699 : ℕ)^8323*100000000000000^6275 ≤ 34656662987009^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498100699 10000000000 34656662987009 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238331883/10000000000 : ℝ)^8323 ≤ (32027342363077/100000000000000 : ℝ)^6275 := by
    have hnat : (4238331883 : ℕ)^8323*100000000000000^6275 ≤ 32027342363077^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238331883 10000000000 32027342363077 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183138499/5000000000 : ℝ), (4498100699/10000000000 : ℝ), (4238331883/10000000000 : ℝ)] ![(2082249665177/6250000000000 : ℝ), (34656662987009/100000000000000 : ℝ), (32027342363077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183138499/5000000000 : ℝ)|^8323 ≤ (2082249665177/6250000000000 : ℝ)^6275
        have hw : |(2183138499/5000000000 : ℝ)|=(2183138499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498100699/10000000000 : ℝ)|^8323 ≤ (34656662987009/100000000000000 : ℝ)^6275
        have hw : |(4498100699/10000000000 : ℝ)|=(4498100699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238331883/10000000000 : ℝ)|^8323 ≤ (32027342363077/100000000000000 : ℝ)^6275
        have hw : |(4238331883/10000000000 : ℝ)|=(4238331883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (697/6250 : ℝ) ^ (4161/1024 : ℝ) ≤ (13456752691011951/100000000000000000000 : ℝ) := by
    have hpowers : (697/6250 : ℝ)^4161 ≤ (13456752691011951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (697 : ℕ)^4161*100000000000000000000^1024 ≤ 13456752691011951^1024*6250^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 6250 13456752691011951 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/6250 : ℝ)) (X := (13456752691011951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4161/1024 : ℝ) ≤ (36292083087418487/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4161 ≤ (36292083087418487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4161*100000000000000000000^1024 ≤ 36292083087418487^1024*25000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36292083087418487 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36292083087418487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013456752691011951/50000000000000000000 : ℝ) ≤ (10000662259889801/10000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50013456752691011951/50000000000000000000 : ℝ)^1024 ≤ (10000662259889801/10000000000000000 : ℝ)^4161 := by
      have hnat : (50013456752691011951 : ℕ)^1024*10000000000000000^4161 ≤ 10000662259889801^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013456752691011951 50000000000000000000 10000662259889801 10000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000662259889801/10000000000000000 : ℝ)) (X := (50013456752691011951/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024874417889215219/50000000000000000000 : ℝ) ≤ (10001224062901527/10000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50024874417889215219/50000000000000000000 : ℝ)^1024 ≤ (10001224062901527/10000000000000000 : ℝ)^4161 := by
      have hnat : (50024874417889215219 : ℕ)^1024*10000000000000000^4161 ≤ 10001224062901527^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024874417889215219 50000000000000000000 10001224062901527 10000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001224062901527/10000000000000000 : ℝ)) (X := (50024874417889215219/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036292083087418487/50000000000000000000 : ℝ) ≤ (10001785865913253/10000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50036292083087418487/50000000000000000000 : ℝ)^1024 ≤ (10001785865913253/10000000000000000 : ℝ)^4161 := by
      have hnat : (50036292083087418487 : ℕ)^1024*10000000000000000^4161 ≤ 10001785865913253^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036292083087418487 50000000000000000000 10001785865913253 10000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001785865913253/10000000000000000 : ℝ)) (X := (50036292083087418487/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13456752691011951/100000000000000000000 : ℝ) ≤ ((1541475597756330479/1542000000000000000 : ℝ)+2*(280901505863/154200000000000 : ℝ)*(697/6250 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (1541475597756330479/1542000000000000000 : ℝ)+2*(280901505863/154200000000000 : ℝ)*(697/6250 : ℝ)=(10000662259889801/10000000000000000 : ℝ) by norm_num, show 1+2*(13456752691011951/100000000000000000000 : ℝ)=(50013456752691011951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36292083087418487/100000000000000000000 : ℝ)+(13456752691011951/100000000000000000000 : ℝ) ≤ ((1541475597756330479/1542000000000000000 : ℝ)+(280901505863/154200000000000 : ℝ)*((3559/25000 : ℝ)+(697/6250 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (1541475597756330479/1542000000000000000 : ℝ)+(280901505863/154200000000000 : ℝ)*((3559/25000 : ℝ)+(697/6250 : ℝ))=(10001224062901527/10000000000000000 : ℝ) by norm_num, show 1+(36292083087418487/100000000000000000000 : ℝ)+(13456752691011951/100000000000000000000 : ℝ)=(50024874417889215219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36292083087418487/100000000000000000000 : ℝ) ≤ ((1541475597756330479/1542000000000000000 : ℝ)+2*(280901505863/154200000000000 : ℝ)*(3559/25000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (1541475597756330479/1542000000000000000 : ℝ)+2*(280901505863/154200000000000 : ℝ)*(3559/25000 : ℝ)=(10001785865913253/10000000000000000 : ℝ) by norm_num, show 1+2*(36292083087418487/100000000000000000000 : ℝ)=(50036292083087418487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1541475597756330479/1542000000000000000 : ℝ)*(X 1 0+X 2 0)+(280901505863/154200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1541475597756330479/1542000000000000000 : ℝ)) (alpha := (280901505863/154200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1541475597756330479/1542000000000000000 : ℝ)*(X 0 1+X 2 1)+(280901505863/154200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1541475597756330479/1542000000000000000 : ℝ)) (alpha := (280901505863/154200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1541475597756330479/1542000000000000000 : ℝ)*(X 0 2+X 1 2)+(280901505863/154200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1541475597756330479/1542000000000000000 : ℝ)) (alpha := (280901505863/154200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1086232933/5000000000 : ℝ)*X 0 0+(539523403/1000000000 : ℝ)*X 0 1+(5263672521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345298677/10000000000 : ℝ)*X 1 0+(-2239227913/10000000000 : ℝ)*X 1 1+(526367247/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668162323/1250000000 : ℝ)*X 2 0+(5263672553/10000000000 : ℝ)*X 2 1+(-2239227927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873253373/2000000000 : ℝ)*X 0 0+(4237653637/10000000000 : ℝ)*X 0 1+(899755181/2000000000 : ℝ)*X 0 2+(873253373/2000000000 : ℝ)*X 1 0+(4237653637/10000000000 : ℝ)*X 1 1+(899755181/2000000000 : ℝ)*X 1 2+(873253373/2000000000 : ℝ)*X 2 0+(4237653637/10000000000 : ℝ)*X 2 1+(899755181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086235363/5000000000 : ℝ)*X 0 0+(16450041/31250000 : ℝ)*X 0 1+(1078978509/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327999293/2500000000 : ℝ)*X 1 0+(-1054003951/5000000000 : ℝ)*X 1 1+(5394892499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132799921/250000000 : ℝ)*X 2 0+(2697446367/5000000000 : ℝ)*X 2 1+(-65875251/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183138499/5000000000 : ℝ)*X 0 0+(4498100699/10000000000 : ℝ)*X 0 1+(4238331883/10000000000 : ℝ)*X 0 2+(2183138499/5000000000 : ℝ)*X 1 0+(4498100699/10000000000 : ℝ)*X 1 1+(4238331883/10000000000 : ℝ)*X 1 2+(2183138499/5000000000 : ℝ)*X 2 0+(4498100699/10000000000 : ℝ)*X 2 1+(4238331883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5028013866273153708477/514000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2118128383/100000000000000 : ℝ)*(base19) + (1940778293/100000000000000 : ℝ)*(base23) + (64326457/25000000000000 : ℝ)*(upper3) + (1506783/6250000000000 : ℝ)*(upper4) + (11138417/6250000000000 : ℝ)*(upper5) + (1143079928394421/20000000000000 : ℝ)*(major0) + (1143079928394421/20000000000000 : ℝ)*(major1) + (1143079928394421/20000000000000 : ℝ)*(major2) + (760106540656747/10000000000000 : ℝ)*(sp0) + (3800558589171139/50000000000000 : ℝ)*(sp1) + (475069834730773/6250000000000 : ℝ)*(sp2) + (1914825503073101/50000000000000 : ℝ)*(sp3) + (53889903191/100000000000000 : ℝ)*(sp4) + (28655256399/100000000000000 : ℝ)*(sp7) + (1914839830701301/50000000000000 : ℝ)*(f.failure) + (7601119296470661/100000000000000 : ℝ)*(f.sum) + (5212302988991/1542000000000000000000000000 : ℝ)*base65 + (660494854329287659/30840000000000000000000000000000 : ℝ)*base67 + (396436436801807659/30840000000000000000000000000000 : ℝ)*base69 + (196120211463167659/30840000000000000000000000000000 : ℝ)*base71 + (589676090861/1542000000000000000000000000 : ℝ)*base73 + (167213404351992341/30840000000000000000000000000000 : ℝ)*base76 + (30968299909872341/30840000000000000000000000000000 : ℝ)*base78 + (362292326797272341/30840000000000000000000000000000 : ℝ)*base80 + (6171072722201/1542000000000000000000000000 : ℝ)*base81 + (59654727/5000000000000000000000 : ℝ)*base89 + (59654727/5000000000000000000000 : ℝ)*base91 + (59654727/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133760726788903572121306767/12850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36371477/10000000000000 : ℝ)*(base19) + (8466061/4000000000000 : ℝ)*(base23) + (19978027/100000000000000 : ℝ)*(lower3) + (16737689/10000000000000 : ℝ)*(lower4) + (22900547/20000000000000 : ℝ)*(lower5) + (2872545324338091/50000000000000 : ℝ)*(major0) + (2872545324338091/50000000000000 : ℝ)*(major1) + (2872545324338091/50000000000000 : ℝ)*(major2) + (2902106447/25000000000000 : ℝ)*(sp1) + (13264497369/100000000000000 : ℝ)*(sp2) + (3820303217216167/50000000000000 : ℝ)*(sp4) + (119384288473309/1562500000000 : ℝ)*(sp5) + (95507411978543/1250000000000 : ℝ)*(sp6) + (1924787257970091/50000000000000 : ℝ)*(sp7) + (1924787257970091/50000000000000 : ℝ)*(f.failure) + (3820303217216167/50000000000000 : ℝ)*(f.sum) + (8968257467809/1285000000000000000000000000 : ℝ)*base66 + (406953914625498137/25700000000000000000000000000000 : ℝ)*base68 + (200324974982098137/25700000000000000000000000000000 : ℝ)*base70 + (187873346775698137/25700000000000000000000000000000 : ℝ)*base72 + (5129286133759/1285000000000000000000000000 : ℝ)*base74 + (740587665019898137/25700000000000000000000000000000 : ℝ)*base76 + (385552996079298137/25700000000000000000000000000000 : ℝ)*base78 + (411742234206398137/25700000000000000000000000000000 : ℝ)*base80 + (511391297559/80312500000000000000000000 : ℝ)*base82 + (57996057/5000000000000000000000 : ℝ)*base89 + (57996057/5000000000000000000000 : ℝ)*base91 + (57996057/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1130_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1130_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1130_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1130_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1130_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1130_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
