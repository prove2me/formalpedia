-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b020
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:26:47.197007+00:00
-- url     : https://prove2.me/submissions/2f0d3323-eeff-43e2-ba16-76b341faedba

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
theorem collision_support_c329047_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-107073399/5000000000 : ℝ)*x 0 + (-597292167/1000000000 : ℝ)*x 1 + (2583749097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107073399/5000000000 : ℝ)^95 ≤ (245792068303/25000000000000 : ℝ)^79 := by
    have hnat : (107073399 : ℕ)^95*25000000000000^79 ≤ 245792068303^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107073399 5000000000 245792068303 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597292167/1000000000 : ℝ)^95 ≤ (5380932790291/10000000000000 : ℝ)^79 := by
    have hnat : (597292167 : ℕ)^95*10000000000000^79 ≤ 5380932790291^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597292167 1000000000 5380932790291 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583749097/5000000000 : ℝ)^95 ≤ (11301875954437/25000000000000 : ℝ)^79 := by
    have hnat : (2583749097 : ℕ)^95*25000000000000^79 ≤ 11301875954437^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583749097 5000000000 11301875954437 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107073399/5000000000 : ℝ), (-597292167/1000000000 : ℝ), (2583749097/5000000000 : ℝ)] ![(245792068303/25000000000000 : ℝ), (5380932790291/10000000000000 : ℝ), (11301875954437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107073399/5000000000 : ℝ)|^95 ≤ (245792068303/25000000000000 : ℝ)^79
        have hw : |(-107073399/5000000000 : ℝ)|=(107073399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-597292167/1000000000 : ℝ)|^95 ≤ (5380932790291/10000000000000 : ℝ)^79
        have hw : |(-597292167/1000000000 : ℝ)|=(597292167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583749097/5000000000 : ℝ)|^95 ≤ (11301875954437/25000000000000 : ℝ)^79
        have hw : |(2583749097/5000000000 : ℝ)|=(2583749097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (640288159/1250000000 : ℝ)*x 0 + (3551101009/10000000000 : ℝ)*x 1 + (3311513551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640288159/1250000000 : ℝ)^95 ≤ (8946496863931/20000000000000 : ℝ)^79 := by
    have hnat : (640288159 : ℕ)^95*20000000000000^79 ≤ 8946496863931^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640288159 1250000000 8946496863931 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3551101009/10000000000 : ℝ)^95 ≤ (28793688992507/100000000000000 : ℝ)^79 := by
    have hnat : (3551101009 : ℕ)^95*100000000000000^79 ≤ 28793688992507^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3551101009 10000000000 28793688992507 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3311513551/10000000000 : ℝ)^95 ≤ (2647382667401/10000000000000 : ℝ)^79 := by
    have hnat : (3311513551 : ℕ)^95*10000000000000^79 ≤ 2647382667401^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311513551 10000000000 2647382667401 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640288159/1250000000 : ℝ), (3551101009/10000000000 : ℝ), (3311513551/10000000000 : ℝ)] ![(8946496863931/20000000000000 : ℝ), (28793688992507/100000000000000 : ℝ), (2647382667401/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640288159/1250000000 : ℝ)|^95 ≤ (8946496863931/20000000000000 : ℝ)^79
        have hw : |(640288159/1250000000 : ℝ)|=(640288159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3551101009/10000000000 : ℝ)|^95 ≤ (28793688992507/100000000000000 : ℝ)^79
        have hw : |(3551101009/10000000000 : ℝ)|=(3551101009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3311513551/10000000000 : ℝ)|^95 ≤ (2647382667401/10000000000000 : ℝ)^79
        have hw : |(3311513551/10000000000 : ℝ)|=(3311513551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5464570031/10000000000 : ℝ)*x 0 + (-174020837/500000000 : ℝ)*x 1 + (-1501862029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464570031/10000000000 : ℝ)^95 ≤ (3021918847657/6250000000000 : ℝ)^79 := by
    have hnat : (5464570031 : ℕ)^95*6250000000000^79 ≤ 3021918847657^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464570031 10000000000 3021918847657 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174020837/500000000 : ℝ)^95 ≤ (28105872474681/100000000000000 : ℝ)^79 := by
    have hnat : (174020837 : ℕ)^95*100000000000000^79 ≤ 28105872474681^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174020837 500000000 28105872474681 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1501862029/5000000000 : ℝ)^95 ≤ (11771712973373/50000000000000 : ℝ)^79 := by
    have hnat : (1501862029 : ℕ)^95*50000000000000^79 ≤ 11771712973373^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501862029 5000000000 11771712973373 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5464570031/10000000000 : ℝ), (-174020837/500000000 : ℝ), (-1501862029/5000000000 : ℝ)] ![(3021918847657/6250000000000 : ℝ), (28105872474681/100000000000000 : ℝ), (11771712973373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5464570031/10000000000 : ℝ)|^95 ≤ (3021918847657/6250000000000 : ℝ)^79
        have hw : |(5464570031/10000000000 : ℝ)|=(5464570031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174020837/500000000 : ℝ)|^95 ≤ (28105872474681/100000000000000 : ℝ)^79
        have hw : |(-174020837/500000000 : ℝ)|=(174020837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1501862029/5000000000 : ℝ)|^95 ≤ (11771712973373/50000000000000 : ℝ)^79
        have hw : |(-1501862029/5000000000 : ℝ)|=(1501862029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-471253803/10000000000 : ℝ)*x 0 + (-3671463033/5000000000 : ℝ)*x 1 + (3519395029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471253803/10000000000 : ℝ)^95 ≤ (634580908029/25000000000000 : ℝ)^79 := by
    have hnat : (471253803 : ℕ)^95*25000000000000^79 ≤ 634580908029^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471253803 10000000000 634580908029 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3671463033/5000000000 : ℝ)^95 ≤ (68976859119361/100000000000000 : ℝ)^79 := by
    have hnat : (3671463033 : ℕ)^95*100000000000000^79 ≤ 68976859119361^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671463033 5000000000 68976859119361 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3519395029/10000000000 : ℝ)^95 ≤ (3560602154579/12500000000000 : ℝ)^79 := by
    have hnat : (3519395029 : ℕ)^95*12500000000000^79 ≤ 3560602154579^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3519395029 10000000000 3560602154579 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471253803/10000000000 : ℝ), (-3671463033/5000000000 : ℝ), (3519395029/10000000000 : ℝ)] ![(634580908029/25000000000000 : ℝ), (68976859119361/100000000000000 : ℝ), (3560602154579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471253803/10000000000 : ℝ)|^95 ≤ (634580908029/25000000000000 : ℝ)^79
        have hw : |(-471253803/10000000000 : ℝ)|=(471253803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3671463033/5000000000 : ℝ)|^95 ≤ (68976859119361/100000000000000 : ℝ)^79
        have hw : |(-3671463033/5000000000 : ℝ)|=(3671463033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3519395029/10000000000 : ℝ)|^95 ≤ (3560602154579/12500000000000 : ℝ)^79
        have hw : |(3519395029/10000000000 : ℝ)|=(3519395029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1676703349/5000000000 : ℝ)*x 0 + (4650618081/10000000000 : ℝ)*x 1 + (1001790409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1676703349/5000000000 : ℝ)^95 ≤ (26877085461609/100000000000000 : ℝ)^79 := by
    have hnat : (1676703349 : ℕ)^95*100000000000000^79 ≤ 26877085461609^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676703349 5000000000 26877085461609 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4650618081/10000000000 : ℝ)^95 ≤ (39826401327673/100000000000000 : ℝ)^79 := by
    have hnat : (4650618081 : ℕ)^95*100000000000000^79 ≤ 39826401327673^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4650618081 10000000000 39826401327673 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001790409/2500000000 : ℝ)^95 ≤ (4162064149809/12500000000000 : ℝ)^79 := by
    have hnat : (1001790409 : ℕ)^95*12500000000000^79 ≤ 4162064149809^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001790409 2500000000 4162064149809 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1676703349/5000000000 : ℝ), (4650618081/10000000000 : ℝ), (1001790409/2500000000 : ℝ)] ![(26877085461609/100000000000000 : ℝ), (39826401327673/100000000000000 : ℝ), (4162064149809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1676703349/5000000000 : ℝ)|^95 ≤ (26877085461609/100000000000000 : ℝ)^79
        have hw : |(1676703349/5000000000 : ℝ)|=(1676703349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4650618081/10000000000 : ℝ)|^95 ≤ (39826401327673/100000000000000 : ℝ)^79
        have hw : |(4650618081/10000000000 : ℝ)|=(4650618081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001790409/2500000000 : ℝ)|^95 ≤ (4162064149809/12500000000000 : ℝ)^79
        have hw : |(1001790409/2500000000 : ℝ)|=(1001790409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4788683257/10000000000 : ℝ)*x 0 + (-3394922491/10000000000 : ℝ)*x 1 + (-3823486353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4788683257/10000000000 : ℝ)^95 ≤ (20626225396203/50000000000000 : ℝ)^79 := by
    have hnat : (4788683257 : ℕ)^95*50000000000000^79 ≤ 20626225396203^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788683257 10000000000 20626225396203 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3394922491/10000000000 : ℝ)^95 ≤ (5455543955657/20000000000000 : ℝ)^79 := by
    have hnat : (3394922491 : ℕ)^95*20000000000000^79 ≤ 5455543955657^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394922491 10000000000 5455543955657 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3823486353/10000000000 : ℝ)^95 ≤ (15734914710083/50000000000000 : ℝ)^79 := by
    have hnat : (3823486353 : ℕ)^95*50000000000000^79 ≤ 15734914710083^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3823486353 10000000000 15734914710083 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4788683257/10000000000 : ℝ), (-3394922491/10000000000 : ℝ), (-3823486353/10000000000 : ℝ)] ![(20626225396203/50000000000000 : ℝ), (5455543955657/20000000000000 : ℝ), (15734914710083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4788683257/10000000000 : ℝ)|^95 ≤ (20626225396203/50000000000000 : ℝ)^79
        have hw : |(4788683257/10000000000 : ℝ)|=(4788683257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3394922491/10000000000 : ℝ)|^95 ≤ (5455543955657/20000000000000 : ℝ)^79
        have hw : |(-3394922491/10000000000 : ℝ)|=(3394922491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3823486353/10000000000 : ℝ)|^95 ≤ (15734914710083/50000000000000 : ℝ)^79
        have hw : |(-3823486353/10000000000 : ℝ)|=(3823486353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5157371649/10000000000 : ℝ)*x 0 + (34163/5000000000 : ℝ)*x 1 + (379583161/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5157371649/10000000000 : ℝ)^95 ≤ (11275247756537/25000000000000 : ℝ)^79 := by
    have hnat : (5157371649 : ℕ)^95*25000000000000^79 ≤ 11275247756537^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157371649 10000000000 11275247756537 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34163/5000000000 : ℝ)^95 ≤ (61436463/100000000000000 : ℝ)^79 := by
    have hnat : (34163 : ℕ)^95*100000000000000^79 ≤ 61436463^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34163 5000000000 61436463 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379583161/625000000 : ℝ)^95 ≤ (54898947525537/100000000000000 : ℝ)^79 := by
    have hnat : (379583161 : ℕ)^95*100000000000000^79 ≤ 54898947525537^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379583161 625000000 54898947525537 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5157371649/10000000000 : ℝ), (34163/5000000000 : ℝ), (379583161/625000000 : ℝ)] ![(11275247756537/25000000000000 : ℝ), (61436463/100000000000000 : ℝ), (54898947525537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5157371649/10000000000 : ℝ)|^95 ≤ (11275247756537/25000000000000 : ℝ)^79
        have hw : |(5157371649/10000000000 : ℝ)|=(5157371649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34163/5000000000 : ℝ)|^95 ≤ (61436463/100000000000000 : ℝ)^79
        have hw : |(34163/5000000000 : ℝ)|=(34163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(379583161/625000000 : ℝ)|^95 ≤ (54898947525537/100000000000000 : ℝ)^79
        have hw : |(379583161/625000000 : ℝ)|=(379583161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-176337/10000000000 : ℝ)*x 0 + (-4870892959/10000000000 : ℝ)*x 1 + (3173822387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176337/10000000000 : ℝ)^95 ≤ (96061103/50000000000000 : ℝ)^79 := by
    have hnat : (176337 : ℕ)^95*50000000000000^79 ≤ 96061103^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176337 10000000000 96061103 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870892959/10000000000 : ℝ)^95 ≤ (42105559106849/100000000000000 : ℝ)^79 := by
    have hnat : (4870892959 : ℕ)^95*100000000000000^79 ≤ 42105559106849^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870892959 10000000000 42105559106849 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173822387/5000000000 : ℝ)^95 ≤ (11578849753017/20000000000000 : ℝ)^79 := by
    have hnat : (3173822387 : ℕ)^95*20000000000000^79 ≤ 11578849753017^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173822387 5000000000 11578849753017 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176337/10000000000 : ℝ), (-4870892959/10000000000 : ℝ), (3173822387/5000000000 : ℝ)] ![(96061103/50000000000000 : ℝ), (42105559106849/100000000000000 : ℝ), (11578849753017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176337/10000000000 : ℝ)|^95 ≤ (96061103/50000000000000 : ℝ)^79
        have hw : |(-176337/10000000000 : ℝ)|=(176337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4870892959/10000000000 : ℝ)|^95 ≤ (42105559106849/100000000000000 : ℝ)^79
        have hw : |(-4870892959/10000000000 : ℝ)|=(4870892959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3173822387/5000000000 : ℝ)|^95 ≤ (11578849753017/20000000000000 : ℝ)^79
        have hw : |(3173822387/5000000000 : ℝ)|=(3173822387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (44042361/125000000 : ℝ)*x 0 + (879483243/2000000000 : ℝ)*x 1 + (4101641861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44042361/125000000 : ℝ)^95 ≤ (3565461678191/12500000000000 : ℝ)^79 := by
    have hnat : (44042361 : ℕ)^95*12500000000000^79 ≤ 3565461678191^79*125000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44042361 125000000 3565461678191 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879483243/2000000000 : ℝ)^95 ≤ (37233493869813/100000000000000 : ℝ)^79 := by
    have hnat : (879483243 : ℕ)^95*100000000000000^79 ≤ 37233493869813^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879483243 2000000000 37233493869813 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4101641861/10000000000 : ℝ)^95 ≤ (1369712508003/4000000000000 : ℝ)^79 := by
    have hnat : (4101641861 : ℕ)^95*4000000000000^79 ≤ 1369712508003^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101641861 10000000000 1369712508003 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44042361/125000000 : ℝ), (879483243/2000000000 : ℝ), (4101641861/10000000000 : ℝ)] ![(3565461678191/12500000000000 : ℝ), (37233493869813/100000000000000 : ℝ), (1369712508003/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44042361/125000000 : ℝ)|^95 ≤ (3565461678191/12500000000000 : ℝ)^79
        have hw : |(44042361/125000000 : ℝ)|=(44042361/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(879483243/2000000000 : ℝ)|^95 ≤ (37233493869813/100000000000000 : ℝ)^79
        have hw : |(879483243/2000000000 : ℝ)|=(879483243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4101641861/10000000000 : ℝ)|^95 ≤ (1369712508003/4000000000000 : ℝ)^79
        have hw : |(4101641861/10000000000 : ℝ)|=(4101641861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3182635071/5000000000 : ℝ)*x 0 + (-2858208749/10000000000 : ℝ)*x 1 + (-2593643537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3182635071/5000000000 : ℝ)^95 ≤ (29043807251401/50000000000000 : ℝ)^79 := by
    have hnat : (3182635071 : ℕ)^95*50000000000000^79 ≤ 29043807251401^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182635071 5000000000 29043807251401 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2858208749/10000000000 : ℝ)^95 ≤ (27723353889/125000000000 : ℝ)^79 := by
    have hnat : (2858208749 : ℕ)^95*125000000000^79 ≤ 27723353889^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858208749 10000000000 27723353889 125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2593643537/10000000000 : ℝ)^95 ≤ (9866851185183/50000000000000 : ℝ)^79 := by
    have hnat : (2593643537 : ℕ)^95*50000000000000^79 ≤ 9866851185183^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593643537 10000000000 9866851185183 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3182635071/5000000000 : ℝ), (-2858208749/10000000000 : ℝ), (-2593643537/10000000000 : ℝ)] ![(29043807251401/50000000000000 : ℝ), (27723353889/125000000000 : ℝ), (9866851185183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3182635071/5000000000 : ℝ)|^95 ≤ (29043807251401/50000000000000 : ℝ)^79
        have hw : |(3182635071/5000000000 : ℝ)|=(3182635071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2858208749/10000000000 : ℝ)|^95 ≤ (27723353889/125000000000 : ℝ)^79
        have hw : |(-2858208749/10000000000 : ℝ)|=(2858208749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2593643537/10000000000 : ℝ)|^95 ≤ (9866851185183/50000000000000 : ℝ)^79
        have hw : |(-2593643537/10000000000 : ℝ)|=(2593643537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2052645121/2500000000 : ℝ)*x 0 + (-7865581/625000000 : ℝ)*x 1 + (268683093/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052645121/2500000000 : ℝ)^95 ≤ (78891799098949/100000000000000 : ℝ)^79 := by
    have hnat : (2052645121 : ℕ)^95*100000000000000^79 ≤ 78891799098949^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052645121 2500000000 78891799098949 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7865581/625000000 : ℝ)^95 ≤ (518812515541/100000000000000 : ℝ)^79 := by
    have hnat : (7865581 : ℕ)^95*100000000000000^79 ≤ 518812515541^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7865581 625000000 518812515541 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268683093/1000000000 : ℝ)^95 ≤ (20589388377553/100000000000000 : ℝ)^79 := by
    have hnat : (268683093 : ℕ)^95*100000000000000^79 ≤ 20589388377553^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268683093 1000000000 20589388377553 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052645121/2500000000 : ℝ), (-7865581/625000000 : ℝ), (268683093/1000000000 : ℝ)] ![(78891799098949/100000000000000 : ℝ), (518812515541/100000000000000 : ℝ), (20589388377553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052645121/2500000000 : ℝ)|^95 ≤ (78891799098949/100000000000000 : ℝ)^79
        have hw : |(2052645121/2500000000 : ℝ)|=(2052645121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7865581/625000000 : ℝ)|^95 ≤ (518812515541/100000000000000 : ℝ)^79
        have hw : |(-7865581/625000000 : ℝ)|=(7865581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268683093/1000000000 : ℝ)|^95 ≤ (20589388377553/100000000000000 : ℝ)^79
        have hw : |(268683093/1000000000 : ℝ)|=(268683093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-200418351/5000000000 : ℝ)*x 0 + (-1903537359/2500000000 : ℝ)*x 1 + (649478301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200418351/5000000000 : ℝ)^95 ≤ (2089412483047/100000000000000 : ℝ)^79 := by
    have hnat : (200418351 : ℕ)^95*100000000000000^79 ≤ 2089412483047^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200418351 5000000000 2089412483047 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903537359/2500000000 : ℝ)^95 ≤ (36025995210631/50000000000000 : ℝ)^79 := by
    have hnat : (1903537359 : ℕ)^95*50000000000000^79 ≤ 36025995210631^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903537359 2500000000 36025995210631 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649478301/2000000000 : ℝ)^95 ≤ (25858597079433/100000000000000 : ℝ)^79 := by
    have hnat : (649478301 : ℕ)^95*100000000000000^79 ≤ 25858597079433^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649478301 2000000000 25858597079433 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200418351/5000000000 : ℝ), (-1903537359/2500000000 : ℝ), (649478301/2000000000 : ℝ)] ![(2089412483047/100000000000000 : ℝ), (36025995210631/50000000000000 : ℝ), (25858597079433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200418351/5000000000 : ℝ)|^95 ≤ (2089412483047/100000000000000 : ℝ)^79
        have hw : |(-200418351/5000000000 : ℝ)|=(200418351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1903537359/2500000000 : ℝ)|^95 ≤ (36025995210631/50000000000000 : ℝ)^79
        have hw : |(-1903537359/2500000000 : ℝ)|=(1903537359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649478301/2000000000 : ℝ)|^95 ≤ (25858597079433/100000000000000 : ℝ)^79
        have hw : |(649478301/2000000000 : ℝ)|=(649478301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6359675207/10000000000 : ℝ)*x 0 + (615938811/2000000000 : ℝ)*x 1 + (237074479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6359675207/10000000000 : ℝ)^95 ≤ (58026221398517/100000000000000 : ℝ)^79 := by
    have hnat : (6359675207 : ℕ)^95*100000000000000^79 ≤ 58026221398517^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6359675207 10000000000 58026221398517 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615938811/2000000000 : ℝ)^95 ≤ (303266322623/1250000000000 : ℝ)^79 := by
    have hnat : (615938811 : ℕ)^95*1250000000000^79 ≤ 303266322623^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615938811 2000000000 303266322623 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237074479/1000000000 : ℝ)^95 ≤ (17712472772711/100000000000000 : ℝ)^79 := by
    have hnat : (237074479 : ℕ)^95*100000000000000^79 ≤ 17712472772711^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237074479 1000000000 17712472772711 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6359675207/10000000000 : ℝ), (615938811/2000000000 : ℝ), (237074479/1000000000 : ℝ)] ![(58026221398517/100000000000000 : ℝ), (303266322623/1250000000000 : ℝ), (17712472772711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6359675207/10000000000 : ℝ)|^95 ≤ (58026221398517/100000000000000 : ℝ)^79
        have hw : |(6359675207/10000000000 : ℝ)|=(6359675207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(615938811/2000000000 : ℝ)|^95 ≤ (303266322623/1250000000000 : ℝ)^79
        have hw : |(615938811/2000000000 : ℝ)|=(615938811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237074479/1000000000 : ℝ)|^95 ≤ (17712472772711/100000000000000 : ℝ)^79
        have hw : |(237074479/1000000000 : ℝ)|=(237074479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2672942577/10000000000 : ℝ)*x 0 + (-5883860161/10000000000 : ℝ)*x 1 + (-3334252391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672942577/10000000000 : ℝ)^95 ≤ (10230736513721/50000000000000 : ℝ)^79 := by
    have hnat : (2672942577 : ℕ)^95*50000000000000^79 ≤ 10230736513721^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672942577 10000000000 10230736513721 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5883860161/10000000000 : ℝ)^95 ≤ (52845946126553/100000000000000 : ℝ)^79 := by
    have hnat : (5883860161 : ℕ)^95*100000000000000^79 ≤ 52845946126553^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5883860161 10000000000 52845946126553 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3334252391/10000000000 : ℝ)^95 ≤ (13346290421333/50000000000000 : ℝ)^79 := by
    have hnat : (3334252391 : ℕ)^95*50000000000000^79 ≤ 13346290421333^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3334252391 10000000000 13346290421333 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672942577/10000000000 : ℝ), (-5883860161/10000000000 : ℝ), (-3334252391/10000000000 : ℝ)] ![(10230736513721/50000000000000 : ℝ), (52845946126553/100000000000000 : ℝ), (13346290421333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672942577/10000000000 : ℝ)|^95 ≤ (10230736513721/50000000000000 : ℝ)^79
        have hw : |(2672942577/10000000000 : ℝ)|=(2672942577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5883860161/10000000000 : ℝ)|^95 ≤ (52845946126553/100000000000000 : ℝ)^79
        have hw : |(-5883860161/10000000000 : ℝ)|=(5883860161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3334252391/10000000000 : ℝ)|^95 ≤ (13346290421333/50000000000000 : ℝ)^79
        have hw : |(-3334252391/10000000000 : ℝ)|=(3334252391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (157660039/200000000 : ℝ)*x 0 + (-1081/2000000000 : ℝ)*x 1 + (1572315189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157660039/200000000 : ℝ)^95 ≤ (75122221206527/100000000000000 : ℝ)^79 := by
    have hnat : (157660039 : ℕ)^95*100000000000000^79 ≤ 75122221206527^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157660039 200000000 75122221206527 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081/2000000000 : ℝ)^95 ≤ (2907291/100000000000000 : ℝ)^79 := by
    have hnat : (1081 : ℕ)^95*100000000000000^79 ≤ 2907291^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081 2000000000 2907291 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572315189/5000000000 : ℝ)^95 ≤ (1554860992219/6250000000000 : ℝ)^79 := by
    have hnat : (1572315189 : ℕ)^95*6250000000000^79 ≤ 1554860992219^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572315189 5000000000 1554860992219 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(157660039/200000000 : ℝ), (-1081/2000000000 : ℝ), (1572315189/5000000000 : ℝ)] ![(75122221206527/100000000000000 : ℝ), (2907291/100000000000000 : ℝ), (1554860992219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(157660039/200000000 : ℝ)|^95 ≤ (75122221206527/100000000000000 : ℝ)^79
        have hw : |(157660039/200000000 : ℝ)|=(157660039/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081/2000000000 : ℝ)|^95 ≤ (2907291/100000000000000 : ℝ)^79
        have hw : |(-1081/2000000000 : ℝ)|=(1081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1572315189/5000000000 : ℝ)|^95 ≤ (1554860992219/6250000000000 : ℝ)^79
        have hw : |(1572315189/5000000000 : ℝ)|=(1572315189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-835586239/5000000000 : ℝ)*x 0 + (-4794406127/10000000000 : ℝ)*x 1 + (5342624639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835586239/5000000000 : ℝ)^95 ≤ (11632109852891/100000000000000 : ℝ)^79 := by
    have hnat : (835586239 : ℕ)^95*100000000000000^79 ≤ 11632109852891^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835586239 5000000000 11632109852891 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794406127/10000000000 : ℝ)^95 ≤ (20655871428731/50000000000000 : ℝ)^79 := by
    have hnat : (4794406127 : ℕ)^95*50000000000000^79 ≤ 20655871428731^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794406127 10000000000 20655871428731 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5342624639/10000000000 : ℝ)^95 ≤ (47056147287057/100000000000000 : ℝ)^79 := by
    have hnat : (5342624639 : ℕ)^95*100000000000000^79 ≤ 47056147287057^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342624639 10000000000 47056147287057 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-835586239/5000000000 : ℝ), (-4794406127/10000000000 : ℝ), (5342624639/10000000000 : ℝ)] ![(11632109852891/100000000000000 : ℝ), (20655871428731/50000000000000 : ℝ), (47056147287057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-835586239/5000000000 : ℝ)|^95 ≤ (11632109852891/100000000000000 : ℝ)^79
        have hw : |(-835586239/5000000000 : ℝ)|=(835586239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4794406127/10000000000 : ℝ)|^95 ≤ (20655871428731/50000000000000 : ℝ)^79
        have hw : |(-4794406127/10000000000 : ℝ)|=(4794406127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5342624639/10000000000 : ℝ)|^95 ≤ (47056147287057/100000000000000 : ℝ)^79
        have hw : |(5342624639/10000000000 : ℝ)|=(5342624639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4857770161/10000000000 : ℝ)*x 0 + (121172829/312500000 : ℝ)*x 1 + (81619817/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4857770161/10000000000 : ℝ)^95 ≤ (20984591981143/50000000000000 : ℝ)^79 := by
    have hnat : (4857770161 : ℕ)^95*50000000000000^79 ≤ 20984591981143^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4857770161 10000000000 20984591981143 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121172829/312500000 : ℝ)^95 ≤ (32005501640219/100000000000000 : ℝ)^79 := by
    have hnat : (121172829 : ℕ)^95*100000000000000^79 ≤ 32005501640219^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121172829 312500000 32005501640219 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81619817/250000000 : ℝ)^95 ≤ (26025314376961/100000000000000 : ℝ)^79 := by
    have hnat : (81619817 : ℕ)^95*100000000000000^79 ≤ 26025314376961^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81619817 250000000 26025314376961 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4857770161/10000000000 : ℝ), (121172829/312500000 : ℝ), (81619817/250000000 : ℝ)] ![(20984591981143/50000000000000 : ℝ), (32005501640219/100000000000000 : ℝ), (26025314376961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4857770161/10000000000 : ℝ)|^95 ≤ (20984591981143/50000000000000 : ℝ)^79
        have hw : |(4857770161/10000000000 : ℝ)|=(4857770161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121172829/312500000 : ℝ)|^95 ≤ (32005501640219/100000000000000 : ℝ)^79
        have hw : |(121172829/312500000 : ℝ)|=(121172829/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81619817/250000000 : ℝ)|^95 ≤ (26025314376961/100000000000000 : ℝ)^79
        have hw : |(81619817/250000000 : ℝ)|=(81619817/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2399301077/5000000000 : ℝ)*x 0 + (-3939819527/10000000000 : ℝ)*x 1 + (-652847719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2399301077/5000000000 : ℝ)^95 ≤ (516940313789/1250000000000 : ℝ)^79 := by
    have hnat : (2399301077 : ℕ)^95*1250000000000^79 ≤ 516940313789^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399301077 5000000000 516940313789 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3939819527/10000000000 : ℝ)^95 ≤ (16312385932923/50000000000000 : ℝ)^79 := by
    have hnat : (3939819527 : ℕ)^95*50000000000000^79 ≤ 16312385932923^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3939819527 10000000000 16312385932923 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652847719/2000000000 : ℝ)^95 ≤ (1040800120639/4000000000000 : ℝ)^79 := by
    have hnat : (652847719 : ℕ)^95*4000000000000^79 ≤ 1040800120639^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652847719 2000000000 1040800120639 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2399301077/5000000000 : ℝ), (-3939819527/10000000000 : ℝ), (-652847719/2000000000 : ℝ)] ![(516940313789/1250000000000 : ℝ), (16312385932923/50000000000000 : ℝ), (1040800120639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2399301077/5000000000 : ℝ)|^95 ≤ (516940313789/1250000000000 : ℝ)^79
        have hw : |(2399301077/5000000000 : ℝ)|=(2399301077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3939819527/10000000000 : ℝ)|^95 ≤ (16312385932923/50000000000000 : ℝ)^79
        have hw : |(-3939819527/10000000000 : ℝ)|=(3939819527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-652847719/2000000000 : ℝ)|^95 ≤ (1040800120639/4000000000000 : ℝ)^79
        have hw : |(-652847719/2000000000 : ℝ)|=(652847719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329047_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5993097607/10000000000 : ℝ)*x 0 + (-163081441/1000000000 : ℝ)*x 1 + (2072416347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5993097607/10000000000 : ℝ)^95 ≤ (5402797784877/10000000000000 : ℝ)^79 := by
    have hnat : (5993097607 : ℕ)^95*10000000000000^79 ≤ 5402797784877^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993097607 10000000000 5402797784877 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163081441/1000000000 : ℝ)^95 ≤ (11295137854509/100000000000000 : ℝ)^79 := by
    have hnat : (163081441 : ℕ)^95*100000000000000^79 ≤ 11295137854509^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163081441 1000000000 11295137854509 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072416347/5000000000 : ℝ)^95 ≤ (34676884286689/100000000000000 : ℝ)^79 := by
    have hnat : (2072416347 : ℕ)^95*100000000000000^79 ≤ 34676884286689^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072416347 5000000000 34676884286689 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5993097607/10000000000 : ℝ), (-163081441/1000000000 : ℝ), (2072416347/5000000000 : ℝ)] ![(5402797784877/10000000000000 : ℝ), (11295137854509/100000000000000 : ℝ), (34676884286689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5993097607/10000000000 : ℝ)|^95 ≤ (5402797784877/10000000000000 : ℝ)^79
        have hw : |(5993097607/10000000000 : ℝ)|=(5993097607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-163081441/1000000000 : ℝ)|^95 ≤ (11295137854509/100000000000000 : ℝ)^79
        have hw : |(-163081441/1000000000 : ℝ)|=(163081441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072416347/5000000000 : ℝ)|^95 ≤ (34676884286689/100000000000000 : ℝ)^79
        have hw : |(2072416347/5000000000 : ℝ)|=(2072416347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329047 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-107073399/5000000000 : ℝ)*X 0 0+(-597292167/1000000000 : ℝ)*X 0 1+(2583749097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((640288159/1250000000 : ℝ)*X 1 0+(3551101009/10000000000 : ℝ)*X 1 1+(3311513551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5464570031/10000000000 : ℝ)*X 2 0+(-174020837/500000000 : ℝ)*X 2 1+(-1501862029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-471253803/10000000000 : ℝ)*X 0 0+(-3671463033/5000000000 : ℝ)*X 0 1+(3519395029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1676703349/5000000000 : ℝ)*X 1 0+(4650618081/10000000000 : ℝ)*X 1 1+(1001790409/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4788683257/10000000000 : ℝ)*X 2 0+(-3394922491/10000000000 : ℝ)*X 2 1+(-3823486353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((5157371649/10000000000 : ℝ)*X 0 0+(34163/5000000000 : ℝ)*X 0 1+(379583161/625000000 : ℝ)*X 0 2+(5157371649/10000000000 : ℝ)*X 1 0+(34163/5000000000 : ℝ)*X 1 1+(379583161/625000000 : ℝ)*X 1 2+(5157371649/10000000000 : ℝ)*X 2 0+(34163/5000000000 : ℝ)*X 2 1+(379583161/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-176337/10000000000 : ℝ)*X 0 0+(-4870892959/10000000000 : ℝ)*X 0 1+(3173822387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((44042361/125000000 : ℝ)*X 1 0+(879483243/2000000000 : ℝ)*X 1 1+(4101641861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3182635071/5000000000 : ℝ)*X 2 0+(-2858208749/10000000000 : ℝ)*X 2 1+(-2593643537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2052645121/2500000000 : ℝ)*X 0 0+(-7865581/625000000 : ℝ)*X 0 1+(268683093/1000000000 : ℝ)*X 0 2+(2052645121/2500000000 : ℝ)*X 1 0+(-7865581/625000000 : ℝ)*X 1 1+(268683093/1000000000 : ℝ)*X 1 2+(2052645121/2500000000 : ℝ)*X 2 0+(-7865581/625000000 : ℝ)*X 2 1+(268683093/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-200418351/5000000000 : ℝ)*X 0 0+(-1903537359/2500000000 : ℝ)*X 0 1+(649478301/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6359675207/10000000000 : ℝ)*X 1 0+(615938811/2000000000 : ℝ)*X 1 1+(237074479/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2672942577/10000000000 : ℝ)*X 2 0+(-5883860161/10000000000 : ℝ)*X 2 1+(-3334252391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((157660039/200000000 : ℝ)*X 0 0+(-1081/2000000000 : ℝ)*X 0 1+(1572315189/5000000000 : ℝ)*X 0 2+(157660039/200000000 : ℝ)*X 1 0+(-1081/2000000000 : ℝ)*X 1 1+(1572315189/5000000000 : ℝ)*X 1 2+(157660039/200000000 : ℝ)*X 2 0+(-1081/2000000000 : ℝ)*X 2 1+(1572315189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((9599/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9599/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12438153615750313068789/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179470286701/500000000000 : ℝ)*(base3) + (4877655321/3906250000 : ℝ)*(base7) + (1006739/250000000000 : ℝ)*(base40) + (139923441449/500000000000 : ℝ)*(base50) + (2228955583719/1000000000000 : ℝ)*(major_s0_0) + (2228955583719/1000000000000 : ℝ)*(major_s0_1) + (2228955583719/1000000000000 : ℝ)*(major_s0_2) + (2934071/200000000000 : ℝ)*(sp_s0_0) + (2788433556979/1000000000000 : ℝ)*(sp_s0_7) + (1573652530749/500000000000 : ℝ)*(sp_s0_8) + (111537218411/40000000000 : ℝ)*(sp_s0_9) + (1892165740663/1000000000000 : ℝ)*(sp_s0_13) + (41869619/500000000000 : ℝ)*(sp_s0_15) + (8883529/500000000000 : ℝ)*(sp_s0_23) + (100242655189/100000000000 : ℝ)*(f.failure) + (1394224113667/500000000000 : ℝ)*(f.sum) + (141693190350383/5000000000000000000000000000 : ℝ)*base63 + (3978810471482081/10000000000000000000000000000 : ℝ)*base65 + (1039165003517919/10000000000000000000000000000 : ℝ)*base66 + (3123482710649617/10000000000000000000000000000 : ℝ)*base68 + (129492569989529/625000000000000000000000000 : ℝ)*base71 + (6785801388517919/10000000000000000000000000000 : ℝ)*base72 + (68160192350383/10000000000000000000000000000 : ℝ)*base75 + (3430548845350383/10000000000000000000000000000 : ℝ)*base77 + (1953931422017919/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (3821/2500000000000000 : ℝ)*base87 + (3821/2500000000000000 : ℝ)*base89 + (3821/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10463/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-10463/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10779915648088159738713/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (855836335067/1000000000000 : ℝ)*(base7) + (158065116051/200000000000 : ℝ)*(base40) + (1188713/500000000000 : ℝ)*(base49) + (39632731001/200000000000 : ℝ)*(base59) + (2564708433699/1000000000000 : ℝ)*(major_s0_0) + (2564708433699/1000000000000 : ℝ)*(major_s0_1) + (2564708433699/1000000000000 : ℝ)*(major_s0_2) + (3656367/1000000000000 : ℝ)*(sp_s0_0) + (28316129/1000000000000 : ℝ)*(sp_s0_1) + (175940406411/50000000000 : ℝ)*(sp_s0_14) + (1759391734229/500000000000 : ℝ)*(sp_s0_15) + (3518811784587/1000000000000 : ℝ)*(sp_s0_16) + (1004592171351/500000000000 : ℝ)*(sp_s0_20) + (76426021/1000000000000 : ℝ)*(sp_s0_27) + (144178054207/125000000000 : ℝ)*(f.failure) + (3518811784587/1000000000000 : ℝ)*(f.sum) + (988231893472757/5000000000000000000000000000 : ℝ)*base62 + (3782176688868101/10000000000000000000000000000 : ℝ)*base65 + (58542754131899/10000000000000000000000000000 : ℝ)*base66 + (4682541883472757/10000000000000000000000000000 : ℝ)*base68 + (51349134399709/625000000000000000000000000 : ℝ)*base71 + (2785803693131899/10000000000000000000000000000 : ℝ)*base72 + (4442164109472757/10000000000000000000000000000 : ℝ)*base74 + (2126338922527243/10000000000000000000000000000 : ℝ)*base77 + (1349682232368101/5000000000000000000000000000 : ℝ)*base79 + (887/781250000000000 : ℝ)*base87 + (887/781250000000000 : ℝ)*base89 + (887/781250000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2293/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2293/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45066185529802901428947/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640427083663/500000000000 : ℝ)*(base7) + (325358985089/1000000000000 : ℝ)*(base40) + (4442751/250000000000 : ℝ)*(base43) + (5744279121/50000000000 : ℝ)*(base50) + (398003870519/200000000000 : ℝ)*(major_s0_0) + (248750197699/125000000000 : ℝ)*(major_s0_1) + (398003870519/200000000000 : ℝ)*(major_s0_2) + (6728053/500000000000 : ℝ)*(sp_s0_2) + (315816439/1000000000000 : ℝ)*(sp_s0_7) + (14961209/500000000000 : ℝ)*(sp_s0_16) + (2400509684507/1000000000000 : ℝ)*(sp_s0_21) + (2400843271949/1000000000000 : ℝ)*(sp_s0_22) + (1200391061211/500000000000 : ℝ)*(sp_s0_23) + (543956026023/250000000000 : ℝ)*(sp_s0_27) + (447484968383/500000000000 : ℝ)*(f.failure) + (2400843271949/1000000000000 : ℝ)*(f.sum) + (2369488064691859/10000000000000000000000000000 : ℝ)*base63 + (459528889844719/2000000000000000000000000000 : ℝ)*base64 + (1021238827845899/1250000000000000000000000000 : ℝ)*base66 + (442557295422017/2000000000000000000000000000 : ℝ)*base68 + (61780833695829/125000000000000000000000000 : ℝ)*base71 + (1415770244244719/2000000000000000000000000000 : ℝ)*base72 + (111147608524757/1250000000000000000000000000 : ℝ)*base74 + (289951617977983/2000000000000000000000000000 : ℝ)*base77 + (8527042975990787/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (5087/12500000000000000 : ℝ)*base87 + (7413/12500000000000000 : ℝ)*base88 + (5087/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (9599/20000 : ℝ) ^ (93/16 : ℝ) ≤ (1402657786103675079/100000000000000000000 : ℝ) := by
    have hpowers : (9599/20000 : ℝ)^93 ≤ (1402657786103675079/100000000000000000000 : ℝ)^16 := by
      have hnat : (9599 : ℕ)^93*100000000000000000000^16 ≤ 1402657786103675079^16*20000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9599 20000 1402657786103675079 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9599/20000 : ℝ)) (X := (1402657786103675079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (101402657786103675079/100000000000000000000 : ℝ) ≤ (10023992806862841/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (101402657786103675079/100000000000000000000 : ℝ)^16 ≤ (10023992806862841/10000000000000000 : ℝ)^93 := by
      have hnat : (101402657786103675079 : ℕ)^16*10000000000000000^93 ≤ 10023992806862841^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101402657786103675079 100000000000000000000 10023992806862841 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023992806862841/10000000000000000 : ℝ)) (X := (101402657786103675079/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (51402657786103675079/50000000000000000000 : ℝ) ≤ (2511928096284977/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (51402657786103675079/50000000000000000000 : ℝ)^16 ≤ (2511928096284977/2500000000000000 : ℝ)^93 := by
      have hnat : (51402657786103675079 : ℕ)^16*2500000000000000^93 ≤ 2511928096284977^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51402657786103675079 50000000000000000000 2511928096284977 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511928096284977/2500000000000000 : ℝ)) (X := (51402657786103675079/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(23992806862841/4799500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23719578277067/4799500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (9599/20000 : ℝ)) (alpha := (23992806862841/4799500000000000 : ℝ)) (beta := (23719578277067/4799500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9599/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(23992806862841/4799500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23719578277067/4799500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10463/25000 : ℝ) ^ (93/16 : ℝ) ≤ (158185079799948223/25000000000000000000 : ℝ) := by
    have hpowers : (10463/25000 : ℝ)^93 ≤ (158185079799948223/25000000000000000000 : ℝ)^16 := by
      have hnat : (10463 : ℕ)^93*25000000000000000000^16 ≤ 158185079799948223^16*25000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10463 25000 158185079799948223 25000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10463/25000 : ℝ)) (X := (158185079799948223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25158185079799948223/25000000000000000000 : ℝ) ≤ (5005428724947397/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (25158185079799948223/25000000000000000000 : ℝ)^16 ≤ (5005428724947397/5000000000000000 : ℝ)^93 := by
      have hnat : (25158185079799948223 : ℕ)^16*5000000000000000^93 ≤ 5005428724947397^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25158185079799948223 25000000000000000000 5005428724947397 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005428724947397/5000000000000000 : ℝ)) (X := (25158185079799948223/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12658185079799948223/12500000000000000000 : ℝ) ≤ (2505414630893971/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (12658185079799948223/12500000000000000000 : ℝ)^16 ≤ (2505414630893971/2500000000000000 : ℝ)^93 := by
      have hnat : (12658185079799948223 : ℕ)^16*2500000000000000^93 ≤ 2505414630893971^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12658185079799948223 12500000000000000000 2505414630893971 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505414630893971/2500000000000000 : ℝ)) (X := (12658185079799948223/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5428724947397/2092600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1080107368109/418520000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (10463/25000 : ℝ)) (alpha := (5428724947397/2092600000000000 : ℝ)) (beta := (1080107368109/418520000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10463/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5428724947397/2092600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1080107368109/418520000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2293/4000 : ℝ) ^ (93/16 : ℝ) ≤ (787779842833348797/20000000000000000000 : ℝ) := by
    have hpowers : (2293/4000 : ℝ)^93 ≤ (787779842833348797/20000000000000000000 : ℝ)^16 := by
      have hnat : (2293 : ℕ)^93*20000000000000000000^16 ≤ 787779842833348797^16*4000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2293 4000 787779842833348797 20000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2293/4000 : ℝ)) (X := (787779842833348797/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20787779842833348797/20000000000000000000 : ℝ) ≤ (10066686805899497/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (20787779842833348797/20000000000000000000 : ℝ)^16 ≤ (10066686805899497/10000000000000000 : ℝ)^93 := by
      have hnat : (20787779842833348797 : ℕ)^16*10000000000000000^93 ≤ 10066686805899497^93*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20787779842833348797 20000000000000000000 10066686805899497 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10066686805899497/10000000000000000 : ℝ)) (X := (20787779842833348797/20000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10787779842833348797/10000000000000000000 : ℝ) ≤ (5065656505856717/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (10787779842833348797/10000000000000000000 : ℝ)^16 ≤ (5065656505856717/5000000000000000 : ℝ)^93 := by
      have hnat : (10787779842833348797 : ℕ)^16*5000000000000000^93 ≤ 5065656505856717^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10787779842833348797 10000000000000000000 5065656505856717 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5065656505856717/5000000000000000 : ℝ)) (X := (10787779842833348797/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(66686805899497/5732500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(64626205813937/5732500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (2293/4000 : ℝ)) (alpha := (66686805899497/5732500000000000 : ℝ)) (beta := (64626205813937/5732500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2293/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(66686805899497/5732500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(64626205813937/5732500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-835586239/5000000000 : ℝ)*X 0 0+(-4794406127/10000000000 : ℝ)*X 0 1+(5342624639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4857770161/10000000000 : ℝ)*X 1 0+(121172829/312500000 : ℝ)*X 1 1+(81619817/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2399301077/5000000000 : ℝ)*X 2 0+(-3939819527/10000000000 : ℝ)*X 2 1+(-652847719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5993097607/10000000000 : ℝ)*X 0 0+(-163081441/1000000000 : ℝ)*X 0 1+(2072416347/5000000000 : ℝ)*X 0 2+(5993097607/10000000000 : ℝ)*X 1 0+(-163081441/1000000000 : ℝ)*X 1 1+(2072416347/5000000000 : ℝ)*X 1 2+(5993097607/10000000000 : ℝ)*X 2 0+(-163081441/1000000000 : ℝ)*X 2 1+(2072416347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-23468500949827779478370816947168389/2302959347410000000000000000000000 : ℝ) := by norm_num
    linear_combination (80859/1000000000000 : ℝ)*(base3) + (56559/250000000000 : ℝ)*(base8) + (11/2000000000 : ℝ)*(base10) + (9657/40000000000 : ℝ)*(base21) + (711060964951/1000000000000 : ℝ)*(base40) + (122963/1000000000000 : ℝ)*(base49) + (406817754111/1000000000000 : ℝ)*(base59) + (14049/1000000000000 : ℝ)*(base60) + (55589/25000 : ℝ)*(major_s1_0) + (55589/25000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (679372228177/200000000000 : ℝ)*(sp_s1_0) + (84921536337/25000000000 : ℝ)*(sp_s1_1) + (679372226239/200000000000 : ℝ)*(sp_s1_2) + (999999919141/1000000000000 : ℝ)*(sp_s1_6) + (169843068631/50000000000 : ℝ)*(f.sum) + (57210915869802063/239916590000000000000000000000 : ℝ)*base62 + (2823119156413/4586000000000000000000000 : ℝ)*base65 + (34802329303847/104630000000000000000000000 : ℝ)*base66 + (19509996773031/22930000000000000000000000 : ℝ)*base68 + (4572259668709559/22010507000000000000000000000 : ℝ)*base71 + (15580762758073/47995000000000000000000000 : ℝ)*base72 + (1323329962671/104630000000000000000000000 : ℝ)*base74 + (643080434137/3839600000000000000000000 : ℝ)*base77 + (201481339049853373/1004343370000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b020 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 := by omega
  rcases hc with rfl
  · exact collision_c329047 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b020 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
