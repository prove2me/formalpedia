-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:02.993993+00:00
-- url     : https://prove2.me/submissions/7f0a991d-929e-43f7-9bec-39aeb1f5b4a1

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c308025_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093490953/2000000000 : ℝ)*x 0 + (3195050223/10000000000 : ℝ)*x 1 + (820297173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093490953/2000000000 : ℝ)^35 ≤ (45718494853611/100000000000000 : ℝ)^27 := by
    have hnat : (1093490953 : ℕ)^35*100000000000000^27 ≤ 45718494853611^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093490953 2000000000 45718494853611 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3195050223/10000000000 : ℝ)^35 ≤ (22785379367481/100000000000000 : ℝ)^27 := by
    have hnat : (3195050223 : ℕ)^35*100000000000000^27 ≤ 22785379367481^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195050223 10000000000 22785379367481 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820297173/2000000000 : ℝ)^35 ≤ (6299225153451/20000000000000 : ℝ)^27 := by
    have hnat : (820297173 : ℕ)^35*20000000000000^27 ≤ 6299225153451^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820297173 2000000000 6299225153451 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093490953/2000000000 : ℝ), (3195050223/10000000000 : ℝ), (820297173/2000000000 : ℝ)] ![(45718494853611/100000000000000 : ℝ), (22785379367481/100000000000000 : ℝ), (6299225153451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093490953/2000000000 : ℝ)|^35 ≤ (45718494853611/100000000000000 : ℝ)^27
        have hw : |(-1093490953/2000000000 : ℝ)|=(1093490953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3195050223/10000000000 : ℝ)|^35 ≤ (22785379367481/100000000000000 : ℝ)^27
        have hw : |(3195050223/10000000000 : ℝ)|=(3195050223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(820297173/2000000000 : ℝ)|^35 ≤ (6299225153451/20000000000000 : ℝ)^27
        have hw : |(820297173/2000000000 : ℝ)|=(820297173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4604551707/10000000000 : ℝ)*x 0 + (-2690790247/10000000000 : ℝ)*x 1 + (1354207681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4604551707/10000000000 : ℝ)^35 ≤ (4574051265123/12500000000000 : ℝ)^27 := by
    have hnat : (4604551707 : ℕ)^35*12500000000000^27 ≤ 4574051265123^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604551707 10000000000 4574051265123 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2690790247/10000000000 : ℝ)^35 ≤ (3647416430467/20000000000000 : ℝ)^27 := by
    have hnat : (2690790247 : ℕ)^35*20000000000000^27 ≤ 3647416430467^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690790247 10000000000 3647416430467 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354207681/2500000000 : ℝ)^35 ≤ (45170507707589/100000000000000 : ℝ)^27 := by
    have hnat : (1354207681 : ℕ)^35*100000000000000^27 ≤ 45170507707589^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354207681 2500000000 45170507707589 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4604551707/10000000000 : ℝ), (-2690790247/10000000000 : ℝ), (1354207681/2500000000 : ℝ)] ![(4574051265123/12500000000000 : ℝ), (3647416430467/20000000000000 : ℝ), (45170507707589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4604551707/10000000000 : ℝ)|^35 ≤ (4574051265123/12500000000000 : ℝ)^27
        have hw : |(4604551707/10000000000 : ℝ)|=(4604551707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2690790247/10000000000 : ℝ)|^35 ≤ (3647416430467/20000000000000 : ℝ)^27
        have hw : |(-2690790247/10000000000 : ℝ)|=(2690790247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354207681/2500000000 : ℝ)|^35 ≤ (45170507707589/100000000000000 : ℝ)^27
        have hw : |(1354207681/2500000000 : ℝ)|=(1354207681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3444332319/10000000000 : ℝ)*x 0 + (3299516771/5000000000 : ℝ)*x 1 + (-2495536889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3444332319/10000000000 : ℝ)^35 ≤ (5023205923949/20000000000000 : ℝ)^27 := by
    have hnat : (3444332319 : ℕ)^35*20000000000000^27 ≤ 5023205923949^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3444332319 10000000000 5023205923949 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3299516771/5000000000 : ℝ)^35 ≤ (58343573784083/100000000000000 : ℝ)^27 := by
    have hnat : (3299516771 : ℕ)^35*100000000000000^27 ≤ 58343573784083^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3299516771 5000000000 58343573784083 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495536889/10000000000 : ℝ)^35 ≤ (16540396578041/100000000000000 : ℝ)^27 := by
    have hnat : (2495536889 : ℕ)^35*100000000000000^27 ≤ 16540396578041^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495536889 10000000000 16540396578041 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3444332319/10000000000 : ℝ), (3299516771/5000000000 : ℝ), (-2495536889/10000000000 : ℝ)] ![(5023205923949/20000000000000 : ℝ), (58343573784083/100000000000000 : ℝ), (16540396578041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3444332319/10000000000 : ℝ)|^35 ≤ (5023205923949/20000000000000 : ℝ)^27
        have hw : |(3444332319/10000000000 : ℝ)|=(3444332319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3299516771/5000000000 : ℝ)|^35 ≤ (58343573784083/100000000000000 : ℝ)^27
        have hw : |(3299516771/5000000000 : ℝ)|=(3299516771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2495536889/10000000000 : ℝ)|^35 ≤ (16540396578041/100000000000000 : ℝ)^27
        have hw : |(-2495536889/10000000000 : ℝ)|=(2495536889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5681811413/10000000000 : ℝ)*x 0 + (274532779/1000000000 : ℝ)*x 1 + (4274289461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5681811413/10000000000 : ℝ)^35 ≤ (9611079353567/20000000000000 : ℝ)^27 := by
    have hnat : (5681811413 : ℕ)^35*20000000000000^27 ≤ 9611079353567^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681811413 10000000000 9611079353567 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274532779/1000000000 : ℝ)^35 ≤ (18717668392033/100000000000000 : ℝ)^27 := by
    have hnat : (274532779 : ℕ)^35*100000000000000^27 ≤ 18717668392033^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274532779 1000000000 18717668392033 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4274289461/10000000000 : ℝ)^35 ≤ (6645386963019/20000000000000 : ℝ)^27 := by
    have hnat : (4274289461 : ℕ)^35*20000000000000^27 ≤ 6645386963019^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274289461 10000000000 6645386963019 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5681811413/10000000000 : ℝ), (274532779/1000000000 : ℝ), (4274289461/10000000000 : ℝ)] ![(9611079353567/20000000000000 : ℝ), (18717668392033/100000000000000 : ℝ), (6645386963019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5681811413/10000000000 : ℝ)|^35 ≤ (9611079353567/20000000000000 : ℝ)^27
        have hw : |(-5681811413/10000000000 : ℝ)|=(5681811413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274532779/1000000000 : ℝ)|^35 ≤ (18717668392033/100000000000000 : ℝ)^27
        have hw : |(274532779/1000000000 : ℝ)|=(274532779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4274289461/10000000000 : ℝ)|^35 ≤ (6645386963019/20000000000000 : ℝ)^27
        have hw : |(4274289461/10000000000 : ℝ)|=(4274289461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4334883/9765625 : ℝ)*x 0 + (-428957953/2000000000 : ℝ)*x 1 + (749331329/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334883/9765625 : ℝ)^35 ≤ (872382463379/2500000000000 : ℝ)^27 := by
    have hnat : (4334883 : ℕ)^35*2500000000000^27 ≤ 872382463379^27*9765625^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334883 9765625 872382463379 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428957953/2000000000 : ℝ)^35 ≤ (6795892560157/50000000000000 : ℝ)^27 := by
    have hnat : (428957953 : ℕ)^35*50000000000000^27 ≤ 6795892560157^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428957953 2000000000 6795892560157 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (749331329/1250000000 : ℝ)^35 ≤ (1609778635211/3125000000000 : ℝ)^27 := by
    have hnat : (749331329 : ℕ)^35*3125000000000^27 ≤ 1609778635211^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749331329 1250000000 1609778635211 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334883/9765625 : ℝ), (-428957953/2000000000 : ℝ), (749331329/1250000000 : ℝ)] ![(872382463379/2500000000000 : ℝ), (6795892560157/50000000000000 : ℝ), (1609778635211/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334883/9765625 : ℝ)|^35 ≤ (872382463379/2500000000000 : ℝ)^27
        have hw : |(4334883/9765625 : ℝ)|=(4334883/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428957953/2000000000 : ℝ)|^35 ≤ (6795892560157/50000000000000 : ℝ)^27
        have hw : |(-428957953/2000000000 : ℝ)|=(428957953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(749331329/1250000000 : ℝ)|^35 ≤ (1609778635211/3125000000000 : ℝ)^27
        have hw : |(749331329/1250000000 : ℝ)|=(749331329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (597557783/2000000000 : ℝ)*x 0 + (7175826427/10000000000 : ℝ)*x 1 + (-220324679/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (597557783/2000000000 : ℝ)^35 ≤ (2611007063033/12500000000000 : ℝ)^27 := by
    have hnat : (597557783 : ℕ)^35*12500000000000^27 ≤ 2611007063033^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597557783 2000000000 2611007063033 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7175826427/10000000000 : ℝ)^35 ≤ (2601520795213/4000000000000 : ℝ)^27 := by
    have hnat : (7175826427 : ℕ)^35*4000000000000^27 ≤ 2601520795213^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7175826427 10000000000 2601520795213 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220324679/1000000000 : ℝ)^35 ≤ (879620225383/6250000000000 : ℝ)^27 := by
    have hnat : (220324679 : ℕ)^35*6250000000000^27 ≤ 879620225383^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220324679 1000000000 879620225383 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(597557783/2000000000 : ℝ), (7175826427/10000000000 : ℝ), (-220324679/1000000000 : ℝ)] ![(2611007063033/12500000000000 : ℝ), (2601520795213/4000000000000 : ℝ), (879620225383/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(597557783/2000000000 : ℝ)|^35 ≤ (2611007063033/12500000000000 : ℝ)^27
        have hw : |(597557783/2000000000 : ℝ)|=(597557783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7175826427/10000000000 : ℝ)|^35 ≤ (2601520795213/4000000000000 : ℝ)^27
        have hw : |(7175826427/10000000000 : ℝ)|=(7175826427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220324679/1000000000 : ℝ)|^35 ≤ (879620225383/6250000000000 : ℝ)^27
        have hw : |(-220324679/1000000000 : ℝ)|=(220324679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2327842527/10000000000 : ℝ)*x 0 + (1118164261/2000000000 : ℝ)*x 1 + (944761913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2327842527/10000000000 : ℝ)^35 ≤ (15114169685063/100000000000000 : ℝ)^27 := by
    have hnat : (2327842527 : ℕ)^35*100000000000000^27 ≤ 15114169685063^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327842527 10000000000 15114169685063 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118164261/2000000000 : ℝ)^35 ≤ (470601785319/1000000000000 : ℝ)^27 := by
    have hnat : (1118164261 : ℕ)^35*1000000000000^27 ≤ 470601785319^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118164261 2000000000 470601785319 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944761913/2000000000 : ℝ)^35 ≤ (18912825886707/50000000000000 : ℝ)^27 := by
    have hnat : (944761913 : ℕ)^35*50000000000000^27 ≤ 18912825886707^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944761913 2000000000 18912825886707 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2327842527/10000000000 : ℝ), (1118164261/2000000000 : ℝ), (944761913/2000000000 : ℝ)] ![(15114169685063/100000000000000 : ℝ), (470601785319/1000000000000 : ℝ), (18912825886707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2327842527/10000000000 : ℝ)|^35 ≤ (15114169685063/100000000000000 : ℝ)^27
        have hw : |(2327842527/10000000000 : ℝ)|=(2327842527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118164261/2000000000 : ℝ)|^35 ≤ (470601785319/1000000000000 : ℝ)^27
        have hw : |(1118164261/2000000000 : ℝ)|=(1118164261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(944761913/2000000000 : ℝ)|^35 ≤ (18912825886707/50000000000000 : ℝ)^27
        have hw : |(944761913/2000000000 : ℝ)|=(944761913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2773269983/5000000000 : ℝ)*x 0 + (2603124759/10000000000 : ℝ)*x 1 + (4542242047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2773269983/5000000000 : ℝ)^35 ≤ (46577573175217/100000000000000 : ℝ)^27 := by
    have hnat : (2773269983 : ℕ)^35*100000000000000^27 ≤ 46577573175217^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773269983 5000000000 46577573175217 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603124759/10000000000 : ℝ)^35 ≤ (17470619741557/100000000000000 : ℝ)^27 := by
    have hnat : (2603124759 : ℕ)^35*100000000000000^27 ≤ 17470619741557^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603124759 10000000000 17470619741557 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542242047/10000000000 : ℝ)^35 ≤ (8987951767387/25000000000000 : ℝ)^27 := by
    have hnat : (4542242047 : ℕ)^35*25000000000000^27 ≤ 8987951767387^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542242047 10000000000 8987951767387 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2773269983/5000000000 : ℝ), (2603124759/10000000000 : ℝ), (4542242047/10000000000 : ℝ)] ![(46577573175217/100000000000000 : ℝ), (17470619741557/100000000000000 : ℝ), (8987951767387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2773269983/5000000000 : ℝ)|^35 ≤ (46577573175217/100000000000000 : ℝ)^27
        have hw : |(-2773269983/5000000000 : ℝ)|=(2773269983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603124759/10000000000 : ℝ)|^35 ≤ (17470619741557/100000000000000 : ℝ)^27
        have hw : |(2603124759/10000000000 : ℝ)|=(2603124759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542242047/10000000000 : ℝ)|^35 ≤ (8987951767387/25000000000000 : ℝ)^27
        have hw : |(4542242047/10000000000 : ℝ)|=(4542242047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (528703299/1000000000 : ℝ)*x 0 + (-1392900921/5000000000 : ℝ)*x 1 + (4658719177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528703299/1000000000 : ℝ)^35 ≤ (10943110276907/25000000000000 : ℝ)^27 := by
    have hnat : (528703299 : ℕ)^35*25000000000000^27 ≤ 10943110276907^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528703299 1000000000 10943110276907 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392900921/5000000000 : ℝ)^35 ≤ (2384520390387/12500000000000 : ℝ)^27 := by
    have hnat : (1392900921 : ℕ)^35*12500000000000^27 ≤ 2384520390387^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392900921 5000000000 2384520390387 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4658719177/10000000000 : ℝ)^35 ≤ (37151395755519/100000000000000 : ℝ)^27 := by
    have hnat : (4658719177 : ℕ)^35*100000000000000^27 ≤ 37151395755519^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4658719177 10000000000 37151395755519 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528703299/1000000000 : ℝ), (-1392900921/5000000000 : ℝ), (4658719177/10000000000 : ℝ)] ![(10943110276907/25000000000000 : ℝ), (2384520390387/12500000000000 : ℝ), (37151395755519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528703299/1000000000 : ℝ)|^35 ≤ (10943110276907/25000000000000 : ℝ)^27
        have hw : |(528703299/1000000000 : ℝ)|=(528703299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1392900921/5000000000 : ℝ)|^35 ≤ (2384520390387/12500000000000 : ℝ)^27
        have hw : |(-1392900921/5000000000 : ℝ)|=(1392900921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4658719177/10000000000 : ℝ)|^35 ≤ (37151395755519/100000000000000 : ℝ)^27
        have hw : |(4658719177/10000000000 : ℝ)|=(4658719177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (387123103/1250000000 : ℝ)*x 0 + (3475591059/5000000000 : ℝ)*x 1 + (-2397852359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387123103/1250000000 : ℝ)^35 ≤ (21882967290689/100000000000000 : ℝ)^27 := by
    have hnat : (387123103 : ℕ)^35*100000000000000^27 ≤ 21882967290689^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387123103 1250000000 21882967290689 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3475591059/5000000000 : ℝ)^35 ≤ (12482202693857/20000000000000 : ℝ)^27 := by
    have hnat : (3475591059 : ℕ)^35*20000000000000^27 ≤ 12482202693857^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3475591059 5000000000 12482202693857 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397852359/10000000000 : ℝ)^35 ≤ (314120384557/2000000000000 : ℝ)^27 := by
    have hnat : (2397852359 : ℕ)^35*2000000000000^27 ≤ 314120384557^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397852359 10000000000 314120384557 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(387123103/1250000000 : ℝ), (3475591059/5000000000 : ℝ), (-2397852359/10000000000 : ℝ)] ![(21882967290689/100000000000000 : ℝ), (12482202693857/20000000000000 : ℝ), (314120384557/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(387123103/1250000000 : ℝ)|^35 ≤ (21882967290689/100000000000000 : ℝ)^27
        have hw : |(387123103/1250000000 : ℝ)|=(387123103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3475591059/5000000000 : ℝ)|^35 ≤ (12482202693857/20000000000000 : ℝ)^27
        have hw : |(3475591059/5000000000 : ℝ)|=(3475591059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2397852359/10000000000 : ℝ)|^35 ≤ (314120384557/2000000000000 : ℝ)^27
        have hw : |(-2397852359/10000000000 : ℝ)|=(2397852359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (40283131/250000000 : ℝ)*x 0 + (262023303/625000000 : ℝ)*x 1 + (823472539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40283131/250000000 : ℝ)^35 ≤ (2345387143249/25000000000000 : ℝ)^27 := by
    have hnat : (40283131 : ℕ)^35*25000000000000^27 ≤ 2345387143249^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40283131 250000000 2345387143249 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262023303/625000000 : ℝ)^35 ≤ (32403816650469/100000000000000 : ℝ)^27 := by
    have hnat : (262023303 : ℕ)^35*100000000000000^27 ≤ 32403816650469^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262023303 625000000 32403816650469 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823472539/1250000000 : ℝ)^35 ≤ (11642926951219/20000000000000 : ℝ)^27 := by
    have hnat : (823472539 : ℕ)^35*20000000000000^27 ≤ 11642926951219^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823472539 1250000000 11642926951219 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40283131/250000000 : ℝ), (262023303/625000000 : ℝ), (823472539/1250000000 : ℝ)] ![(2345387143249/25000000000000 : ℝ), (32403816650469/100000000000000 : ℝ), (11642926951219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40283131/250000000 : ℝ)|^35 ≤ (2345387143249/25000000000000 : ℝ)^27
        have hw : |(40283131/250000000 : ℝ)|=(40283131/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262023303/625000000 : ℝ)|^35 ≤ (32403816650469/100000000000000 : ℝ)^27
        have hw : |(262023303/625000000 : ℝ)|=(262023303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(823472539/1250000000 : ℝ)|^35 ≤ (11642926951219/20000000000000 : ℝ)^27
        have hw : |(823472539/1250000000 : ℝ)|=(823472539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1478657479/2500000000 : ℝ)*x 0 + (2796529949/10000000000 : ℝ)*x 1 + (992797433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1478657479/2500000000 : ℝ)^35 ≤ (2531165633509/5000000000000 : ℝ)^27 := by
    have hnat : (1478657479 : ℕ)^35*5000000000000^27 ≤ 2531165633509^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478657479 2500000000 2531165633509 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796529949/10000000000 : ℝ)^35 ≤ (299553846493/1562500000000 : ℝ)^27 := by
    have hnat : (2796529949 : ℕ)^35*1562500000000^27 ≤ 299553846493^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796529949 10000000000 299553846493 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992797433/2500000000 : ℝ)^35 ≤ (7551310282773/25000000000000 : ℝ)^27 := by
    have hnat : (992797433 : ℕ)^35*25000000000000^27 ≤ 7551310282773^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992797433 2500000000 7551310282773 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1478657479/2500000000 : ℝ), (2796529949/10000000000 : ℝ), (992797433/2500000000 : ℝ)] ![(2531165633509/5000000000000 : ℝ), (299553846493/1562500000000 : ℝ), (7551310282773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1478657479/2500000000 : ℝ)|^35 ≤ (2531165633509/5000000000000 : ℝ)^27
        have hw : |(-1478657479/2500000000 : ℝ)|=(1478657479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796529949/10000000000 : ℝ)|^35 ≤ (299553846493/1562500000000 : ℝ)^27
        have hw : |(2796529949/10000000000 : ℝ)|=(2796529949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(992797433/2500000000 : ℝ)|^35 ≤ (7551310282773/25000000000000 : ℝ)^27
        have hw : |(992797433/2500000000 : ℝ)|=(992797433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1035837449/2500000000 : ℝ)*x 0 + (-101421807/312500000 : ℝ)*x 1 + (5385644521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035837449/2500000000 : ℝ)^35 ≤ (7978372412099/25000000000000 : ℝ)^27 := by
    have hnat : (1035837449 : ℕ)^35*25000000000000^27 ≤ 7978372412099^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035837449 2500000000 7978372412099 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101421807/312500000 : ℝ)^35 ≤ (1453301780063/6250000000000 : ℝ)^27 := by
    have hnat : (101421807 : ℕ)^35*6250000000000^27 ≤ 1453301780063^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101421807 312500000 1453301780063 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385644521/10000000000 : ℝ)^35 ≤ (44833681863533/100000000000000 : ℝ)^27 := by
    have hnat : (5385644521 : ℕ)^35*100000000000000^27 ≤ 44833681863533^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385644521 10000000000 44833681863533 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035837449/2500000000 : ℝ), (-101421807/312500000 : ℝ), (5385644521/10000000000 : ℝ)] ![(7978372412099/25000000000000 : ℝ), (1453301780063/6250000000000 : ℝ), (44833681863533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035837449/2500000000 : ℝ)|^35 ≤ (7978372412099/25000000000000 : ℝ)^27
        have hw : |(1035837449/2500000000 : ℝ)|=(1035837449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101421807/312500000 : ℝ)|^35 ≤ (1453301780063/6250000000000 : ℝ)^27
        have hw : |(-101421807/312500000 : ℝ)|=(101421807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385644521/10000000000 : ℝ)|^35 ≤ (44833681863533/100000000000000 : ℝ)^27
        have hw : |(5385644521/10000000000 : ℝ)|=(5385644521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3841617359/10000000000 : ℝ)*x 0 + (252779453/400000000 : ℝ)*x 1 + (-2421377111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3841617359/10000000000 : ℝ)^35 ≤ (14466956569089/50000000000000 : ℝ)^27 := by
    have hnat : (3841617359 : ℕ)^35*50000000000000^27 ≤ 14466956569089^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841617359 10000000000 14466956569089 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252779453/400000000 : ℝ)^35 ≤ (344750214367/625000000000 : ℝ)^27 := by
    have hnat : (252779453 : ℕ)^35*625000000000^27 ≤ 344750214367^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252779453 400000000 344750214367 625000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2421377111/10000000000 : ℝ)^35 ≤ (636242101863/4000000000000 : ℝ)^27 := by
    have hnat : (2421377111 : ℕ)^35*4000000000000^27 ≤ 636242101863^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421377111 10000000000 636242101863 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3841617359/10000000000 : ℝ), (252779453/400000000 : ℝ), (-2421377111/10000000000 : ℝ)] ![(14466956569089/50000000000000 : ℝ), (344750214367/625000000000 : ℝ), (636242101863/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3841617359/10000000000 : ℝ)|^35 ≤ (14466956569089/50000000000000 : ℝ)^27
        have hw : |(3841617359/10000000000 : ℝ)|=(3841617359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252779453/400000000 : ℝ)|^35 ≤ (344750214367/625000000000 : ℝ)^27
        have hw : |(252779453/400000000 : ℝ)|=(252779453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2421377111/10000000000 : ℝ)|^35 ≤ (636242101863/4000000000000 : ℝ)^27
        have hw : |(-2421377111/10000000000 : ℝ)|=(2421377111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s0_26 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1677401683/10000000000 : ℝ)*x 0 + (2480004747/5000000000 : ℝ)*x 1 + (5842219563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1677401683/10000000000 : ℝ)^35 ≤ (988325296227/10000000000000 : ℝ)^27 := by
    have hnat : (1677401683 : ℕ)^35*10000000000000^27 ≤ 988325296227^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677401683 10000000000 988325296227 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2480004747/5000000000 : ℝ)^35 ≤ (40295365803549/100000000000000 : ℝ)^27 := by
    have hnat : (2480004747 : ℕ)^35*100000000000000^27 ≤ 40295365803549^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480004747 5000000000 40295365803549 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5842219563/10000000000 : ℝ)^35 ≤ (12455345303101/25000000000000 : ℝ)^27 := by
    have hnat : (5842219563 : ℕ)^35*25000000000000^27 ≤ 12455345303101^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5842219563 10000000000 12455345303101 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1677401683/10000000000 : ℝ), (2480004747/5000000000 : ℝ), (5842219563/10000000000 : ℝ)] ![(988325296227/10000000000000 : ℝ), (40295365803549/100000000000000 : ℝ), (12455345303101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1677401683/10000000000 : ℝ)|^35 ≤ (988325296227/10000000000000 : ℝ)^27
        have hw : |(1677401683/10000000000 : ℝ)|=(1677401683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2480004747/5000000000 : ℝ)|^35 ≤ (40295365803549/100000000000000 : ℝ)^27
        have hw : |(2480004747/5000000000 : ℝ)|=(2480004747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5842219563/10000000000 : ℝ)|^35 ≤ (12455345303101/25000000000000 : ℝ)^27
        have hw : |(5842219563/10000000000 : ℝ)|=(5842219563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2423151781/5000000000 : ℝ)*x 0 + (1997942549/5000000000 : ℝ)*x 1 + (3995894399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2423151781/5000000000 : ℝ)^35 ≤ (7820399506513/20000000000000 : ℝ)^27 := by
    have hnat : (2423151781 : ℕ)^35*20000000000000^27 ≤ 7820399506513^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423151781 5000000000 7820399506513 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997942549/5000000000 : ℝ)^35 ≤ (30448955288381/100000000000000 : ℝ)^27 := by
    have hnat : (1997942549 : ℕ)^35*100000000000000^27 ≤ 30448955288381^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997942549 5000000000 30448955288381 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3995894399/10000000000 : ℝ)^35 ≤ (30449047162561/100000000000000 : ℝ)^27 := by
    have hnat : (3995894399 : ℕ)^35*100000000000000^27 ≤ 30449047162561^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3995894399 10000000000 30449047162561 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2423151781/5000000000 : ℝ), (1997942549/5000000000 : ℝ), (3995894399/10000000000 : ℝ)] ![(7820399506513/20000000000000 : ℝ), (30448955288381/100000000000000 : ℝ), (30449047162561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2423151781/5000000000 : ℝ)|^35 ≤ (7820399506513/20000000000000 : ℝ)^27
        have hw : |(-2423151781/5000000000 : ℝ)|=(2423151781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1997942549/5000000000 : ℝ)|^35 ≤ (30448955288381/100000000000000 : ℝ)^27
        have hw : |(1997942549/5000000000 : ℝ)|=(1997942549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3995894399/10000000000 : ℝ)|^35 ≤ (30449047162561/100000000000000 : ℝ)^27
        have hw : |(3995894399/10000000000 : ℝ)|=(3995894399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2067853917/5000000000 : ℝ)*x 0 + (-426247889/1250000000 : ℝ)*x 1 + (5249585799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067853917/5000000000 : ℝ)^35 ≤ (31837209221567/100000000000000 : ℝ)^27 := by
    have hnat : (2067853917 : ℕ)^35*100000000000000^27 ≤ 31837209221567^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067853917 5000000000 31837209221567 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426247889/1250000000 : ℝ)^35 ≤ (24791821931133/100000000000000 : ℝ)^27 := by
    have hnat : (426247889 : ℕ)^35*100000000000000^27 ≤ 24791821931133^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426247889 1250000000 24791821931133 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5249585799/10000000000 : ℝ)^35 ≤ (1355342775871/3125000000000 : ℝ)^27 := by
    have hnat : (5249585799 : ℕ)^35*3125000000000^27 ≤ 1355342775871^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249585799 10000000000 1355342775871 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067853917/5000000000 : ℝ), (-426247889/1250000000 : ℝ), (5249585799/10000000000 : ℝ)] ![(31837209221567/100000000000000 : ℝ), (24791821931133/100000000000000 : ℝ), (1355342775871/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067853917/5000000000 : ℝ)|^35 ≤ (31837209221567/100000000000000 : ℝ)^27
        have hw : |(2067853917/5000000000 : ℝ)|=(2067853917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426247889/1250000000 : ℝ)|^35 ≤ (24791821931133/100000000000000 : ℝ)^27
        have hw : |(-426247889/1250000000 : ℝ)|=(426247889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5249585799/10000000000 : ℝ)|^35 ≤ (1355342775871/3125000000000 : ℝ)^27
        have hw : |(5249585799/10000000000 : ℝ)|=(5249585799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1033925073/2500000000 : ℝ)*x 0 + (5249591313/10000000000 : ℝ)*x 1 + (-3409984831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033925073/2500000000 : ℝ)^35 ≤ (15918566979777/50000000000000 : ℝ)^27 := by
    have hnat : (1033925073 : ℕ)^35*50000000000000^27 ≤ 15918566979777^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033925073 2500000000 15918566979777 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5249591313/10000000000 : ℝ)^35 ≤ (43371027881311/100000000000000 : ℝ)^27 := by
    have hnat : (5249591313 : ℕ)^35*100000000000000^27 ≤ 43371027881311^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249591313 10000000000 43371027881311 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3409984831/10000000000 : ℝ)^35 ≤ (24791838131931/100000000000000 : ℝ)^27 := by
    have hnat : (3409984831 : ℕ)^35*100000000000000^27 ≤ 24791838131931^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3409984831 10000000000 24791838131931 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033925073/2500000000 : ℝ), (5249591313/10000000000 : ℝ), (-3409984831/10000000000 : ℝ)] ![(15918566979777/50000000000000 : ℝ), (43371027881311/100000000000000 : ℝ), (24791838131931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033925073/2500000000 : ℝ)|^35 ≤ (15918566979777/50000000000000 : ℝ)^27
        have hw : |(1033925073/2500000000 : ℝ)|=(1033925073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5249591313/10000000000 : ℝ)|^35 ≤ (43371027881311/100000000000000 : ℝ)^27
        have hw : |(5249591313/10000000000 : ℝ)|=(5249591313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3409984831/10000000000 : ℝ)|^35 ≤ (24791838131931/100000000000000 : ℝ)^27
        have hw : |(-3409984831/10000000000 : ℝ)|=(3409984831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308025_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3626245979/10000000000 : ℝ)*x 0 + (2301461427/5000000000 : ℝ)*x 1 + (2301454813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3626245979/10000000000 : ℝ)^35 ≤ (13424437040341/50000000000000 : ℝ)^27 := by
    have hnat : (3626245979 : ℕ)^35*50000000000000^27 ≤ 13424437040341^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3626245979 10000000000 13424437040341 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2301461427/5000000000 : ℝ)^35 ≤ (36575631082499/100000000000000 : ℝ)^27 := by
    have hnat : (2301461427 : ℕ)^35*100000000000000^27 ≤ 36575631082499^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301461427 5000000000 36575631082499 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2301454813/5000000000 : ℝ)^35 ≤ (7315098965251/20000000000000 : ℝ)^27 := by
    have hnat : (2301454813 : ℕ)^35*20000000000000^27 ≤ 7315098965251^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301454813 5000000000 7315098965251 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3626245979/10000000000 : ℝ), (2301461427/5000000000 : ℝ), (2301454813/5000000000 : ℝ)] ![(13424437040341/50000000000000 : ℝ), (36575631082499/100000000000000 : ℝ), (7315098965251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3626245979/10000000000 : ℝ)|^35 ≤ (13424437040341/50000000000000 : ℝ)^27
        have hw : |(3626245979/10000000000 : ℝ)|=(3626245979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2301461427/5000000000 : ℝ)|^35 ≤ (36575631082499/100000000000000 : ℝ)^27
        have hw : |(2301461427/5000000000 : ℝ)|=(2301461427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2301454813/5000000000 : ℝ)|^35 ≤ (7315098965251/20000000000000 : ℝ)^27
        have hw : |(2301454813/5000000000 : ℝ)|=(2301454813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308025 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1093490953/2000000000 : ℝ)*X 0 0+(3195050223/10000000000 : ℝ)*X 0 1+(820297173/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4604551707/10000000000 : ℝ)*X 1 0+(-2690790247/10000000000 : ℝ)*X 1 1+(1354207681/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3444332319/10000000000 : ℝ)*X 2 0+(3299516771/5000000000 : ℝ)*X 2 1+(-2495536889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5681811413/10000000000 : ℝ)*X 0 0+(274532779/1000000000 : ℝ)*X 0 1+(4274289461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4334883/9765625 : ℝ)*X 1 0+(-428957953/2000000000 : ℝ)*X 1 1+(749331329/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((597557783/2000000000 : ℝ)*X 2 0+(7175826427/10000000000 : ℝ)*X 2 1+(-220324679/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2327842527/10000000000 : ℝ)*X 0 0+(1118164261/2000000000 : ℝ)*X 0 1+(944761913/2000000000 : ℝ)*X 0 2+(2327842527/10000000000 : ℝ)*X 1 0+(1118164261/2000000000 : ℝ)*X 1 1+(944761913/2000000000 : ℝ)*X 1 2+(2327842527/10000000000 : ℝ)*X 2 0+(1118164261/2000000000 : ℝ)*X 2 1+(944761913/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2773269983/5000000000 : ℝ)*X 0 0+(2603124759/10000000000 : ℝ)*X 0 1+(4542242047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((528703299/1000000000 : ℝ)*X 1 0+(-1392900921/5000000000 : ℝ)*X 1 1+(4658719177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((387123103/1250000000 : ℝ)*X 2 0+(3475591059/5000000000 : ℝ)*X 2 1+(-2397852359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((40283131/250000000 : ℝ)*X 0 0+(262023303/625000000 : ℝ)*X 0 1+(823472539/1250000000 : ℝ)*X 0 2+(40283131/250000000 : ℝ)*X 1 0+(262023303/625000000 : ℝ)*X 1 1+(823472539/1250000000 : ℝ)*X 1 2+(40283131/250000000 : ℝ)*X 2 0+(262023303/625000000 : ℝ)*X 2 1+(823472539/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1478657479/2500000000 : ℝ)*X 0 0+(2796529949/10000000000 : ℝ)*X 0 1+(992797433/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((1035837449/2500000000 : ℝ)*X 1 0+(-101421807/312500000 : ℝ)*X 1 1+(5385644521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3841617359/10000000000 : ℝ)*X 2 0+(252779453/400000000 : ℝ)*X 2 1+(-2421377111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((1677401683/10000000000 : ℝ)*X 0 0+(2480004747/5000000000 : ℝ)*X 0 1+(5842219563/10000000000 : ℝ)*X 0 2+(1677401683/10000000000 : ℝ)*X 1 0+(2480004747/5000000000 : ℝ)*X 1 1+(5842219563/10000000000 : ℝ)*X 1 2+(1677401683/10000000000 : ℝ)*X 2 0+(2480004747/5000000000 : ℝ)*X 2 1+(5842219563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2111/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2111/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2754026221664472593943/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1493489992063/1000000000000 : ℝ)*(base50) + (1199596878147/1000000000000 : ℝ)*(base59) + (23372116319/100000000000 : ℝ)*(base60) + (1593619530737/250000000000 : ℝ)*(major_s0_0) + (1593619530737/250000000000 : ℝ)*(major_s0_1) + (1593619530737/250000000000 : ℝ)*(major_s0_2) + (293509089/1000000000000 : ℝ)*(sp_s0_0) + (4853243/250000000000 : ℝ)*(sp_s0_1) + (8680670180199/1000000000000 : ℝ)*(sp_s0_7) + (8681266197089/1000000000000 : ℝ)*(sp_s0_8) + (8681285610061/1000000000000 : ℝ)*(sp_s0_9) + (8135243829/2000000000 : ℝ)*(sp_s0_12) + (321920773/1000000000000 : ℝ)*(sp_s0_13) + (42846077/1000000000000 : ℝ)*(sp_s0_26) + (4067664760577/1000000000000 : ℝ)*(f.failure) + (8681285610061/1000000000000 : ℝ)*(f.sum) + (354873926841551/1250000000000000000000000000 : ℝ)*base63 + (23953929270769/312500000000000000000000000 : ℝ)*base65 + (21705560770769/312500000000000000000000000 : ℝ)*base66 + (79501281283449/2500000000000000000000000000 : ℝ)*base68 + (645645352949601/2500000000000000000000000000 : ℝ)*base71 + (44258995802019/312500000000000000000000000 : ℝ)*base72 + (203003662033449/2500000000000000000000000000 : ℝ)*base74 + (278476960716551/2500000000000000000000000000 : ℝ)*base76 + (9258587981803/78125000000000000000000000 : ℝ)*base79 + (17753/100000000000000000 : ℝ)*base86 + (17753/100000000000000000 : ℝ)*base88 + (17753/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2957/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2957/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (454623470847111939363/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (71780656881/250000000000 : ℝ)*(base40) + (359428024649/1000000000000 : ℝ)*(base50) + (533676493447/500000000000 : ℝ)*(base59) + (192093/62500000000 : ℝ)*(base60) + (911578344233/200000000000 : ℝ)*(major_s0_0) + (911578344233/200000000000 : ℝ)*(major_s0_1) + (911578344233/200000000000 : ℝ)*(major_s0_2) + (2456601/20000000000 : ℝ)*(sp_s0_2) + (5574937/250000000000 : ℝ)*(sp_s0_8) + (248291453013/40000000000 : ℝ)*(sp_s0_13) + (3103644582469/500000000000 : ℝ)*(sp_s0_14) + (1551797158659/250000000000 : ℝ)*(sp_s0_15) + (181779347061/62500000000 : ℝ)*(sp_s0_19) + (157121/6250000000 : ℝ)*(sp_s0_20) + (181779347061/62500000000 : ℝ)*(f.failure) + (3103655732343/500000000000 : ℝ)*(f.sum) + (475672943666241/1000000000000000000000000000 : ℝ)*base62 + (171223518850621/250000000000000000000000000 : ℝ)*base65 + (218133724399379/250000000000000000000000000 : ℝ)*base67 + (448020885866241/2000000000000000000000000000 : ℝ)*base68 + (23655192328791/2000000000000000000000000000 : ℝ)*base70 + (173602100224379/250000000000000000000000000 : ℝ)*base73 + (451752358533759/2000000000000000000000000000 : ℝ)*base75 + (746199568533759/2000000000000000000000000000 : ℝ)*base76 + (127911385349379/125000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (4879/6250000000000000 : ℝ)*base86 + (4879/6250000000000000 : ℝ)*base88 + (4879/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7637/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7637/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7726175455473197527827/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4538771/1000000000000 : ℝ)*(base40) + (127117589651/100000000000 : ℝ)*(base50) + (1219508201089/1000000000000 : ℝ)*(base59) + (6598976343557/1000000000000 : ℝ)*(major_s0_0) + (6598976343557/1000000000000 : ℝ)*(major_s0_1) + (6598976343557/1000000000000 : ℝ)*(major_s0_2) + (1209817/500000000000 : ℝ)*(sp_s0_1) + (18592127/500000000000 : ℝ)*(sp_s0_9) + (31231109/500000000000 : ℝ)*(sp_s0_12) + (42283299/1000000000000 : ℝ)*(sp_s0_14) + (8987027607803/1000000000000 : ℝ)*(sp_s0_20) + (898698290487/100000000000 : ℝ)*(sp_s0_21) + (179739808471/20000000000 : ℝ)*(sp_s0_22) + (2105429248231/500000000000 : ℝ)*(sp_s0_26) + (105273023967/25000000000 : ℝ)*(f.failure) + (8987027607803/1000000000000 : ℝ)*(f.sum) + (1838403354382589/5000000000000000000000000000 : ℝ)*base62 + (926111841967609/1250000000000000000000000000 : ℝ)*base65 + (592408553407391/1250000000000000000000000000 : ℝ)*base67 + (4386478387617411/10000000000000000000000000000 : ℝ)*base69 + (1725111431123461/10000000000000000000000000000 : ℝ)*base71 + (630758751782391/1250000000000000000000000000 : ℝ)*base73 + (1236285295617411/10000000000000000000000000000 : ℝ)*base75 + (1133723513617411/10000000000000000000000000000 : ℝ)*base76 + (87719027032391/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (37/2500000000000000 : ℝ)*base87 + (37/2500000000000000 : ℝ)*base89 + (37/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (2111/10000 : ℝ) ^ (17/4 : ℝ) ≤ (134609276980780853/100000000000000000000 : ℝ) := by
    have hpowers : (2111/10000 : ℝ)^17 ≤ (134609276980780853/100000000000000000000 : ℝ)^4 := by
      have hnat : (2111 : ℕ)^17*100000000000000000000^4 ≤ 134609276980780853^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2111 10000 134609276980780853 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2111/10000 : ℝ)) (X := (134609276980780853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100134609276980780853/100000000000000000000 : ℝ) ≤ (625197853015801/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100134609276980780853/100000000000000000000 : ℝ)^4 ≤ (625197853015801/625000000000000 : ℝ)^17 := by
      have hnat : (100134609276980780853 : ℕ)^4*625000000000000^17 ≤ 625197853015801^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100134609276980780853 100000000000000000000 625197853015801 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625197853015801/625000000000000 : ℝ)) (X := (100134609276980780853/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50134609276980780853/50000000000000000000 : ℝ) ≤ (5003164021974569/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50134609276980780853/50000000000000000000 : ℝ)^4 ≤ (5003164021974569/5000000000000000 : ℝ)^17 := by
      have hnat : (50134609276980780853 : ℕ)^4*5000000000000000^17 ≤ 5003164021974569^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50134609276980780853 50000000000000000000 5003164021974569 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003164021974569/5000000000000000 : ℝ)) (X := (50134609276980780853/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(197853015801/131937500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1581197848161/1055500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (2111/10000 : ℝ)) (alpha := (197853015801/131937500000000 : ℝ)) (beta := (1581197848161/1055500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2111/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(197853015801/131937500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1581197848161/1055500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2957/25000 : ℝ) ^ (17/4 : ℝ) ≤ (717386351324731/6250000000000000000 : ℝ) := by
    have hpowers : (2957/25000 : ℝ)^17 ≤ (717386351324731/6250000000000000000 : ℝ)^4 := by
      have hnat : (2957 : ℕ)^17*6250000000000000000^4 ≤ 717386351324731^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2957 25000 717386351324731 6250000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2957/25000 : ℝ)) (X := (717386351324731/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (6250717386351324731/6250000000000000000 : ℝ) ≤ (1250033757876207/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (6250717386351324731/6250000000000000000 : ℝ)^4 ≤ (1250033757876207/1250000000000000 : ℝ)^17 := by
      have hnat : (6250717386351324731 : ℕ)^4*1250000000000000^17 ≤ 1250033757876207^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250717386351324731 6250000000000000000 1250033757876207 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250033757876207/1250000000000000 : ℝ)) (X := (6250717386351324731/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3125717386351324731/3125000000000000000 : ℝ) ≤ (1250067512789809/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3125717386351324731/3125000000000000000 : ℝ)^4 ≤ (1250067512789809/1250000000000000 : ℝ)^17 := by
      have hnat : (3125717386351324731 : ℕ)^4*1250000000000000^17 ≤ 1250067512789809^17*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125717386351324731 3125000000000000000 1250067512789809 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250067512789809/1250000000000000 : ℝ)) (X := (3125717386351324731/3125000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(33757876207/147850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(16877456801/73925000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (2957/25000 : ℝ)) (alpha := (33757876207/147850000000000 : ℝ)) (beta := (16877456801/73925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (2957/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(33757876207/147850000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(16877456801/73925000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7637/100000 : ℝ) ^ (17/4 : ℝ) ≤ (71528950241723/4000000000000000000 : ℝ) := by
    have hpowers : (7637/100000 : ℝ)^17 ≤ (71528950241723/4000000000000000000 : ℝ)^4 := by
      have hnat : (7637 : ℕ)^17*4000000000000000000^4 ≤ 71528950241723^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7637 100000 71528950241723 4000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7637/100000 : ℝ)) (X := (71528950241723/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4000071528950241723/4000000000000000000 : ℝ) ≤ (10000042075565401/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (4000071528950241723/4000000000000000000 : ℝ)^4 ≤ (10000042075565401/10000000000000000 : ℝ)^17 := by
      have hnat : (4000071528950241723 : ℕ)^4*10000000000000000^17 ≤ 10000042075565401^17*4000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000071528950241723 4000000000000000000 10000042075565401 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042075565401/10000000000000000 : ℝ)) (X := (4000071528950241723/4000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2000071528950241723/2000000000000000000 : ℝ) ≤ (5000042075277723/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2000071528950241723/2000000000000000000 : ℝ)^4 ≤ (5000042075277723/5000000000000000 : ℝ)^17 := by
      have hnat : (2000071528950241723 : ℕ)^4*5000000000000000^17 ≤ 5000042075277723^17*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000071528950241723 2000000000000000000 5000042075277723 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042075277723/5000000000000000 : ℝ)) (X := (2000071528950241723/2000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(42075565401/763700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(8414998009/152740000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (7637/100000 : ℝ)) (alpha := (42075565401/763700000000000 : ℝ)) (beta := (8414998009/152740000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7637/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(42075565401/763700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(8414998009/152740000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2423151781/5000000000 : ℝ)*X 0 0+(1997942549/5000000000 : ℝ)*X 0 1+(3995894399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2067853917/5000000000 : ℝ)*X 1 0+(-426247889/1250000000 : ℝ)*X 1 1+(5249585799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1033925073/2500000000 : ℝ)*X 2 0+(5249591313/10000000000 : ℝ)*X 2 1+(-3409984831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3626245979/10000000000 : ℝ)*X 0 0+(2301461427/5000000000 : ℝ)*X 0 1+(2301454813/5000000000 : ℝ)*X 0 2+(3626245979/10000000000 : ℝ)*X 1 0+(2301461427/5000000000 : ℝ)*X 1 1+(2301454813/5000000000 : ℝ)*X 1 2+(3626245979/10000000000 : ℝ)*X 2 0+(2301461427/5000000000 : ℝ)*X 2 1+(2301454813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308025_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-15108639710258100866756643372071151/2383594379950000000000000000000000 : ℝ) := by norm_num
    linear_combination (53279/500000000000 : ℝ)*(base3) + (40903/1000000000000 : ℝ)*(base8) + (36771/500000000000 : ℝ)*(base13) + (33705857869/500000000000 : ℝ)*(base49) + (82577493371/250000000000 : ℝ)*(base50) + (18257/500000000000 : ℝ)*(base53) + (593034715903/1000000000000 : ℝ)*(base59) + (330579822723/1000000000000 : ℝ)*(base60) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (783554981743/500000000000 : ℝ)*(major_s1_2) + (528216222449/250000000000 : ℝ)*(sp_s1_0) + (2112865110799/1000000000000 : ℝ)*(sp_s1_1) + (528216260189/250000000000 : ℝ)*(sp_s1_2) + (499999946721/500000000000 : ℝ)*(sp_s1_6) + (528216260189/250000000000 : ℝ)*(f.sum) + (430035784266843921/1129130450000000000000000000000 : ℝ)*base62 + (12562407444101/76370000000000000000000000 : ℝ)*base65 + (2575618206233/1848125000000000000000000 : ℝ)*base67 + (31690087446483/381850000000000000000000000 : ℝ)*base68 + (21821430100665883/161217070000000000000000000000 : ℝ)*base71 + (16043232227677/21110000000000000000000000 : ℝ)*base73 + (462690362021/2957000000000000000000000 : ℝ)*base75 + (4176730431/20615234375000000000000 : ℝ)*base77 + (4236640043230561/7802783750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p008_b014 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=25 := by omega
  rcases hc with rfl
  · exact collision_c308025 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b014 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
