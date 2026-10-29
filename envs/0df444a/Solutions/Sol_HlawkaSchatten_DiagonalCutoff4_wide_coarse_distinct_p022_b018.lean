-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:20.795851+00:00
-- url     : https://prove2.me/submissions/c1d16e77-c819-44b4-9a1c-43c7f936de78

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
theorem collision_support_c322036_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (144209/10000000000 : ℝ)*x 0 + (-2852848357/5000000000 : ℝ)*x 1 + (-5705696713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144209/10000000000 : ℝ)^21 ≤ (261741/250000000000 : ℝ)^17 := by
    have hnat : (144209 : ℕ)^21*250000000000^17 ≤ 261741^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144209 10000000000 261741 250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852848357/5000000000 : ℝ)^21 ≤ (49999947650217/100000000000000 : ℝ)^17 := by
    have hnat : (2852848357 : ℕ)^21*100000000000000^17 ≤ 49999947650217^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852848357 5000000000 49999947650217 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705696713/10000000000 : ℝ)^21 ≤ (1562498363731/3125000000000 : ℝ)^17 := by
    have hnat : (5705696713 : ℕ)^21*3125000000000^17 ≤ 1562498363731^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705696713 10000000000 1562498363731 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(144209/10000000000 : ℝ), (-2852848357/5000000000 : ℝ), (-5705696713/10000000000 : ℝ)] ![(261741/250000000000 : ℝ), (49999947650217/100000000000000 : ℝ), (1562498363731/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(144209/10000000000 : ℝ)|^21 ≤ (261741/250000000000 : ℝ)^17
        have hw : |(144209/10000000000 : ℝ)|=(144209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2852848357/5000000000 : ℝ)|^21 ≤ (49999947650217/100000000000000 : ℝ)^17
        have hw : |(-2852848357/5000000000 : ℝ)|=(2852848357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5705696713/10000000000 : ℝ)|^21 ≤ (1562498363731/3125000000000 : ℝ)^17
        have hw : |(-5705696713/10000000000 : ℝ)|=(5705696713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2897425721/5000000000 : ℝ)*x 0 + (3204449043/10000000000 : ℝ)*x 1 + (-801112261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2897425721/5000000000 : ℝ)^21 ≤ (25483411066021/50000000000000 : ℝ)^17 := by
    have hnat : (2897425721 : ℕ)^21*50000000000000^17 ≤ 25483411066021^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897425721 5000000000 25483411066021 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3204449043/10000000000 : ℝ)^21 ≤ (24516588919117/100000000000000 : ℝ)^17 := by
    have hnat : (3204449043 : ℕ)^21*100000000000000^17 ≤ 24516588919117^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3204449043 10000000000 24516588919117 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801112261/2500000000 : ℝ)^21 ≤ (3064573616071/12500000000000 : ℝ)^17 := by
    have hnat : (801112261 : ℕ)^21*12500000000000^17 ≤ 3064573616071^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801112261 2500000000 3064573616071 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2897425721/5000000000 : ℝ), (3204449043/10000000000 : ℝ), (-801112261/2500000000 : ℝ)] ![(25483411066021/50000000000000 : ℝ), (24516588919117/100000000000000 : ℝ), (3064573616071/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2897425721/5000000000 : ℝ)|^21 ≤ (25483411066021/50000000000000 : ℝ)^17
        have hw : |(2897425721/5000000000 : ℝ)|=(2897425721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3204449043/10000000000 : ℝ)|^21 ≤ (24516588919117/100000000000000 : ℝ)^17
        have hw : |(3204449043/10000000000 : ℝ)|=(3204449043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-801112261/2500000000 : ℝ)|^21 ≤ (3064573616071/12500000000000 : ℝ)^17
        have hw : |(-801112261/2500000000 : ℝ)|=(801112261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (72435643/125000000 : ℝ)*x 0 + (-801112261/2500000000 : ℝ)*x 1 + (1602224523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72435643/125000000 : ℝ)^21 ≤ (50966822110313/100000000000000 : ℝ)^17 := by
    have hnat : (72435643 : ℕ)^21*100000000000000^17 ≤ 50966822110313^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72435643 125000000 50966822110313 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801112261/2500000000 : ℝ)^21 ≤ (3064573616071/12500000000000 : ℝ)^17 := by
    have hnat : (801112261 : ℕ)^21*12500000000000^17 ≤ 3064573616071^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801112261 2500000000 3064573616071 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602224523/5000000000 : ℝ)^21 ≤ (2451658894747/10000000000000 : ℝ)^17 := by
    have hnat : (1602224523 : ℕ)^21*10000000000000^17 ≤ 2451658894747^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602224523 5000000000 2451658894747 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(72435643/125000000 : ℝ), (-801112261/2500000000 : ℝ), (1602224523/5000000000 : ℝ)] ![(50966822110313/100000000000000 : ℝ), (3064573616071/12500000000000 : ℝ), (2451658894747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(72435643/125000000 : ℝ)|^21 ≤ (50966822110313/100000000000000 : ℝ)^17
        have hw : |(72435643/125000000 : ℝ)|=(72435643/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-801112261/2500000000 : ℝ)|^21 ≤ (3064573616071/12500000000000 : ℝ)^17
        have hw : |(-801112261/2500000000 : ℝ)|=(801112261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1602224523/5000000000 : ℝ)|^21 ≤ (2451658894747/10000000000000 : ℝ)^17
        have hw : |(1602224523/5000000000 : ℝ)|=(1602224523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7795851/5000000000 : ℝ)*x 0 + (-6908276663/10000000000 : ℝ)*x 1 + (-4436307493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7795851/5000000000 : ℝ)^21 ≤ (17036010103/50000000000000 : ℝ)^17 := by
    have hnat : (7795851 : ℕ)^21*50000000000000^17 ≤ 17036010103^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7795851 5000000000 17036010103 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6908276663/10000000000 : ℝ)^21 ≤ (7915609760419/12500000000000 : ℝ)^17 := by
    have hnat : (6908276663 : ℕ)^21*12500000000000^17 ≤ 7915609760419^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6908276663 10000000000 7915609760419 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436307493/10000000000 : ℝ)^21 ≤ (2290065617687/6250000000000 : ℝ)^17 := by
    have hnat : (4436307493 : ℕ)^21*6250000000000^17 ≤ 2290065617687^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436307493 10000000000 2290065617687 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7795851/5000000000 : ℝ), (-6908276663/10000000000 : ℝ), (-4436307493/10000000000 : ℝ)] ![(17036010103/50000000000000 : ℝ), (7915609760419/12500000000000 : ℝ), (2290065617687/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7795851/5000000000 : ℝ)|^21 ≤ (17036010103/50000000000000 : ℝ)^17
        have hw : |(7795851/5000000000 : ℝ)|=(7795851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6908276663/10000000000 : ℝ)|^21 ≤ (7915609760419/12500000000000 : ℝ)^17
        have hw : |(-6908276663/10000000000 : ℝ)|=(6908276663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4436307493/10000000000 : ℝ)|^21 ≤ (2290065617687/6250000000000 : ℝ)^17
        have hw : |(-4436307493/10000000000 : ℝ)|=(4436307493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (971603141/2500000000 : ℝ)*x 0 + (6115501741/10000000000 : ℝ)*x 1 + (-2084320783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971603141/2500000000 : ℝ)^21 ≤ (15557584794173/50000000000000 : ℝ)^17 := by
    have hnat : (971603141 : ℕ)^21*50000000000000^17 ≤ 15557584794173^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971603141 2500000000 15557584794173 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6115501741/10000000000 : ℝ)^21 ≤ (54472940832863/100000000000000 : ℝ)^17 := by
    have hnat : (6115501741 : ℕ)^21*100000000000000^17 ≤ 54472940832863^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6115501741 10000000000 54472940832863 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084320783/10000000000 : ℝ)^21 ≤ (900743098219/6250000000000 : ℝ)^17 := by
    have hnat : (2084320783 : ℕ)^21*6250000000000^17 ≤ 900743098219^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084320783 10000000000 900743098219 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(971603141/2500000000 : ℝ), (6115501741/10000000000 : ℝ), (-2084320783/10000000000 : ℝ)] ![(15557584794173/50000000000000 : ℝ), (54472940832863/100000000000000 : ℝ), (900743098219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(971603141/2500000000 : ℝ)|^21 ≤ (15557584794173/50000000000000 : ℝ)^17
        have hw : |(971603141/2500000000 : ℝ)|=(971603141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6115501741/10000000000 : ℝ)|^21 ≤ (54472940832863/100000000000000 : ℝ)^17
        have hw : |(6115501741/10000000000 : ℝ)|=(6115501741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084320783/10000000000 : ℝ)|^21 ≤ (900743098219/6250000000000 : ℝ)^17
        have hw : |(-2084320783/10000000000 : ℝ)|=(2084320783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5081492499/10000000000 : ℝ)*x 0 + (-145977633/2000000000 : ℝ)*x 1 + (5956148543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5081492499/10000000000 : ℝ)^21 ≤ (21666201252681/50000000000000 : ℝ)^17 := by
    have hnat : (5081492499 : ℕ)^21*50000000000000^17 ≤ 21666201252681^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081492499 10000000000 21666201252681 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145977633/2000000000 : ℝ)^21 ≤ (788528176487/20000000000000 : ℝ)^17 := by
    have hnat : (145977633 : ℕ)^21*20000000000000^17 ≤ 788528176487^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145977633 2000000000 788528176487 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5956148543/10000000000 : ℝ)^21 ≤ (52724956600259/100000000000000 : ℝ)^17 := by
    have hnat : (5956148543 : ℕ)^21*100000000000000^17 ≤ 52724956600259^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956148543 10000000000 52724956600259 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5081492499/10000000000 : ℝ), (-145977633/2000000000 : ℝ), (5956148543/10000000000 : ℝ)] ![(21666201252681/50000000000000 : ℝ), (788528176487/20000000000000 : ℝ), (52724956600259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5081492499/10000000000 : ℝ)|^21 ≤ (21666201252681/50000000000000 : ℝ)^17
        have hw : |(5081492499/10000000000 : ℝ)|=(5081492499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145977633/2000000000 : ℝ)|^21 ≤ (788528176487/20000000000000 : ℝ)^17
        have hw : |(-145977633/2000000000 : ℝ)|=(145977633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5956148543/10000000000 : ℝ)|^21 ≤ (52724956600259/100000000000000 : ℝ)^17
        have hw : |(5956148543/10000000000 : ℝ)|=(5956148543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2778558221/5000000000 : ℝ)*x 0 + (-1123272047/5000000000 : ℝ)*x 1 + (-1088264101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2778558221/5000000000 : ℝ)^21 ≤ (9679302887237/20000000000000 : ℝ)^17 := by
    have hnat : (2778558221 : ℕ)^21*20000000000000^17 ≤ 9679302887237^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778558221 5000000000 9679302887237 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123272047/5000000000 : ℝ)^21 ≤ (15809940256337/100000000000000 : ℝ)^17 := by
    have hnat : (1123272047 : ℕ)^21*100000000000000^17 ≤ 15809940256337^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123272047 5000000000 15809940256337 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088264101/2500000000 : ℝ)^21 ≤ (35793545295971/100000000000000 : ℝ)^17 := by
    have hnat : (1088264101 : ℕ)^21*100000000000000^17 ≤ 35793545295971^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088264101 2500000000 35793545295971 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2778558221/5000000000 : ℝ), (-1123272047/5000000000 : ℝ), (-1088264101/2500000000 : ℝ)] ![(9679302887237/20000000000000 : ℝ), (15809940256337/100000000000000 : ℝ), (35793545295971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2778558221/5000000000 : ℝ)|^21 ≤ (9679302887237/20000000000000 : ℝ)^17
        have hw : |(2778558221/5000000000 : ℝ)|=(2778558221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123272047/5000000000 : ℝ)|^21 ≤ (15809940256337/100000000000000 : ℝ)^17
        have hw : |(-1123272047/5000000000 : ℝ)|=(1123272047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088264101/2500000000 : ℝ)|^21 ≤ (35793545295971/100000000000000 : ℝ)^17
        have hw : |(-1088264101/2500000000 : ℝ)|=(1088264101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1055669/5000000000 : ℝ)*x 0 + (-890340591/2000000000 : ℝ)*x 1 + (-3448575751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055669/5000000000 : ℝ)^21 ≤ (2882357373/100000000000000 : ℝ)^17 := by
    have hnat : (1055669 : ℕ)^21*100000000000000^17 ≤ 2882357373^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055669 5000000000 2882357373 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890340591/2000000000 : ℝ)^21 ≤ (7359637957613/20000000000000 : ℝ)^17 := by
    have hnat : (890340591 : ℕ)^21*20000000000000^17 ≤ 7359637957613^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890340591 2000000000 7359637957613 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3448575751/5000000000 : ℝ)^21 ≤ (63198927844503/100000000000000 : ℝ)^17 := by
    have hnat : (3448575751 : ℕ)^21*100000000000000^17 ≤ 63198927844503^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448575751 5000000000 63198927844503 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055669/5000000000 : ℝ), (-890340591/2000000000 : ℝ), (-3448575751/5000000000 : ℝ)] ![(2882357373/100000000000000 : ℝ), (7359637957613/20000000000000 : ℝ), (63198927844503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055669/5000000000 : ℝ)|^21 ≤ (2882357373/100000000000000 : ℝ)^17
        have hw : |(1055669/5000000000 : ℝ)|=(1055669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890340591/2000000000 : ℝ)|^21 ≤ (7359637957613/20000000000000 : ℝ)^17
        have hw : |(-890340591/2000000000 : ℝ)|=(890340591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3448575751/5000000000 : ℝ)|^21 ≤ (63198927844503/100000000000000 : ℝ)^17
        have hw : |(-3448575751/5000000000 : ℝ)|=(3448575751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (34276339/156250000 : ℝ)*x 0 + (3716959173/10000000000 : ℝ)*x 1 + (-1236304763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34276339/156250000 : ℝ)^21 ≤ (614068199487/4000000000000 : ℝ)^17 := by
    have hnat : (34276339 : ℕ)^21*4000000000000^17 ≤ 614068199487^17*156250000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34276339 156250000 614068199487 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3716959173/10000000000 : ℝ)^21 ≤ (29447979786471/100000000000000 : ℝ)^17 := by
    have hnat : (3716959173 : ℕ)^21*100000000000000^17 ≤ 29447979786471^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716959173 10000000000 29447979786471 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236304763/2000000000 : ℝ)^21 ≤ (55200315218347/100000000000000 : ℝ)^17 := by
    have hnat : (1236304763 : ℕ)^21*100000000000000^17 ≤ 55200315218347^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236304763 2000000000 55200315218347 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34276339/156250000 : ℝ), (3716959173/10000000000 : ℝ), (-1236304763/2000000000 : ℝ)] ![(614068199487/4000000000000 : ℝ), (29447979786471/100000000000000 : ℝ), (55200315218347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34276339/156250000 : ℝ)|^21 ≤ (614068199487/4000000000000 : ℝ)^17
        have hw : |(34276339/156250000 : ℝ)|=(34276339/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3716959173/10000000000 : ℝ)|^21 ≤ (29447979786471/100000000000000 : ℝ)^17
        have hw : |(3716959173/10000000000 : ℝ)|=(3716959173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1236304763/2000000000 : ℝ)|^21 ≤ (55200315218347/100000000000000 : ℝ)^17
        have hw : |(-1236304763/2000000000 : ℝ)|=(1236304763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4024833591/5000000000 : ℝ)*x 0 + (-114367479/1000000000 : ℝ)*x 1 + (146369111/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024833591/5000000000 : ℝ)^21 ≤ (76490592410463/100000000000000 : ℝ)^17 := by
    have hnat : (4024833591 : ℕ)^21*100000000000000^17 ≤ 76490592410463^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024833591 5000000000 76490592410463 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114367479/1000000000 : ℝ)^21 ≤ (1716590424851/25000000000000 : ℝ)^17 := by
    have hnat : (114367479 : ℕ)^21*25000000000000^17 ≤ 1716590424851^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114367479 1000000000 1716590424851 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146369111/625000000 : ℝ)^21 ≤ (8321522934797/50000000000000 : ℝ)^17 := by
    have hnat : (146369111 : ℕ)^21*50000000000000^17 ≤ 8321522934797^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146369111 625000000 8321522934797 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024833591/5000000000 : ℝ), (-114367479/1000000000 : ℝ), (146369111/625000000 : ℝ)] ![(76490592410463/100000000000000 : ℝ), (1716590424851/25000000000000 : ℝ), (8321522934797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024833591/5000000000 : ℝ)|^21 ≤ (76490592410463/100000000000000 : ℝ)^17
        have hw : |(4024833591/5000000000 : ℝ)|=(4024833591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114367479/1000000000 : ℝ)|^21 ≤ (1716590424851/25000000000000 : ℝ)^17
        have hw : |(-114367479/1000000000 : ℝ)|=(114367479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146369111/625000000 : ℝ)|^21 ≤ (8321522934797/50000000000000 : ℝ)^17
        have hw : |(146369111/625000000 : ℝ)|=(146369111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_17 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999999/10000000000 : ℝ)*x 0 + (41/10000000000 : ℝ)*x 1 + (41/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999999/10000000000 : ℝ)^21 ≤ (1562499999807/1562500000000 : ℝ)^17 := by
    have hnat : (9999999999 : ℕ)^21*1562500000000^17 ≤ 1562499999807^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 1562499999807 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41/10000000000 : ℝ)^21 ≤ (4359/100000000000000 : ℝ)^17 := by
    have hnat : (41 : ℕ)^21*100000000000000^17 ≤ 4359^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41 10000000000 4359 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41/10000000000 : ℝ)^21 ≤ (4359/100000000000000 : ℝ)^17 := by
    have hnat : (41 : ℕ)^21*100000000000000^17 ≤ 4359^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41 10000000000 4359 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999999/10000000000 : ℝ), (41/10000000000 : ℝ), (41/10000000000 : ℝ)] ![(1562499999807/1562500000000 : ℝ), (4359/100000000000000 : ℝ), (4359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999999/10000000000 : ℝ)|^21 ≤ (1562499999807/1562500000000 : ℝ)^17
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41/10000000000 : ℝ)|^21 ≤ (4359/100000000000000 : ℝ)^17
        have hw : |(41/10000000000 : ℝ)|=(41/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41/10000000000 : ℝ)|^21 ≤ (4359/100000000000000 : ℝ)^17
        have hw : |(41/10000000000 : ℝ)|=(41/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7189823787/10000000000 : ℝ)*x 0 + (-914627913/5000000000 : ℝ)*x 1 + (-2849419527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7189823787/10000000000 : ℝ)^21 ≤ (66528065123589/100000000000000 : ℝ)^17 := by
    have hnat : (7189823787 : ℕ)^21*100000000000000^17 ≤ 66528065123589^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7189823787 10000000000 66528065123589 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914627913/5000000000 : ℝ)^21 ≤ (1533211177873/12500000000000 : ℝ)^17 := by
    have hnat : (914627913 : ℕ)^21*12500000000000^17 ≤ 1533211177873^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914627913 5000000000 1533211177873 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2849419527/10000000000 : ℝ)^21 ≤ (21206245436103/100000000000000 : ℝ)^17 := by
    have hnat : (2849419527 : ℕ)^21*100000000000000^17 ≤ 21206245436103^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849419527 10000000000 21206245436103 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7189823787/10000000000 : ℝ), (-914627913/5000000000 : ℝ), (-2849419527/10000000000 : ℝ)] ![(66528065123589/100000000000000 : ℝ), (1533211177873/12500000000000 : ℝ), (21206245436103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7189823787/10000000000 : ℝ)|^21 ≤ (66528065123589/100000000000000 : ℝ)^17
        have hw : |(7189823787/10000000000 : ℝ)|=(7189823787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914627913/5000000000 : ℝ)|^21 ≤ (1533211177873/12500000000000 : ℝ)^17
        have hw : |(-914627913/5000000000 : ℝ)|=(914627913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2849419527/10000000000 : ℝ)|^21 ≤ (21206245436103/100000000000000 : ℝ)^17
        have hw : |(-2849419527/10000000000 : ℝ)|=(2849419527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4380871/10000000000 : ℝ)*x 0 + (-7249916381/10000000000 : ℝ)*x 1 + (-4053636317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380871/10000000000 : ℝ)^21 ≤ (3550662573/50000000000000 : ℝ)^17 := by
    have hnat : (4380871 : ℕ)^21*50000000000000^17 ≤ 3550662573^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380871 10000000000 3550662573 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7249916381/10000000000 : ℝ)^21 ≤ (33607807252161/50000000000000 : ℝ)^17 := by
    have hnat : (7249916381 : ℕ)^21*50000000000000^17 ≤ 33607807252161^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7249916381 10000000000 33607807252161 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4053636317/10000000000 : ℝ)^21 ≤ (32777284161507/100000000000000 : ℝ)^17 := by
    have hnat : (4053636317 : ℕ)^21*100000000000000^17 ≤ 32777284161507^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053636317 10000000000 32777284161507 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380871/10000000000 : ℝ), (-7249916381/10000000000 : ℝ), (-4053636317/10000000000 : ℝ)] ![(3550662573/50000000000000 : ℝ), (33607807252161/50000000000000 : ℝ), (32777284161507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380871/10000000000 : ℝ)|^21 ≤ (3550662573/50000000000000 : ℝ)^17
        have hw : |(4380871/10000000000 : ℝ)|=(4380871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7249916381/10000000000 : ℝ)|^21 ≤ (33607807252161/50000000000000 : ℝ)^17
        have hw : |(-7249916381/10000000000 : ℝ)|=(7249916381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4053636317/10000000000 : ℝ)|^21 ≤ (32777284161507/100000000000000 : ℝ)^17
        have hw : |(-4053636317/10000000000 : ℝ)|=(4053636317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3820729767/5000000000 : ℝ)*x 0 + (3122137357/10000000000 : ℝ)*x 1 + (-32675261/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3820729767/5000000000 : ℝ)^21 ≤ (14345589126551/20000000000000 : ℝ)^17 := by
    have hnat : (3820729767 : ℕ)^21*20000000000000^17 ≤ 14345589126551^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3820729767 5000000000 14345589126551 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122137357/10000000000 : ℝ)^21 ≤ (23741028889429/100000000000000 : ℝ)^17 := by
    have hnat : (3122137357 : ℕ)^21*100000000000000^17 ≤ 23741028889429^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122137357 10000000000 23741028889429 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32675261/400000000 : ℝ)^21 ≤ (906205093277/20000000000000 : ℝ)^17 := by
    have hnat : (32675261 : ℕ)^21*20000000000000^17 ≤ 906205093277^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32675261 400000000 906205093277 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3820729767/5000000000 : ℝ), (3122137357/10000000000 : ℝ), (-32675261/400000000 : ℝ)] ![(14345589126551/20000000000000 : ℝ), (23741028889429/100000000000000 : ℝ), (906205093277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3820729767/5000000000 : ℝ)|^21 ≤ (14345589126551/20000000000000 : ℝ)^17
        have hw : |(3820729767/5000000000 : ℝ)|=(3820729767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122137357/10000000000 : ℝ)|^21 ≤ (23741028889429/100000000000000 : ℝ)^17
        have hw : |(3122137357/10000000000 : ℝ)|=(3122137357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32675261/400000000 : ℝ)|^21 ≤ (906205093277/20000000000000 : ℝ)^17
        have hw : |(-32675261/400000000 : ℝ)|=(32675261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (706491871/2500000000 : ℝ)*x 0 + (-1270980421/2500000000 : ℝ)*x 1 + (433903287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (706491871/2500000000 : ℝ)^21 ≤ (1311928114693/6250000000000 : ℝ)^17 := by
    have hnat : (706491871 : ℕ)^21*6250000000000^17 ≤ 1311928114693^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706491871 2500000000 1311928114693 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270980421/2500000000 : ℝ)^21 ≤ (10839498223259/25000000000000 : ℝ)^17 := by
    have hnat : (1270980421 : ℕ)^21*25000000000000^17 ≤ 10839498223259^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270980421 2500000000 10839498223259 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433903287/1000000000 : ℝ)^21 ≤ (35651157259469/100000000000000 : ℝ)^17 := by
    have hnat : (433903287 : ℕ)^21*100000000000000^17 ≤ 35651157259469^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433903287 1000000000 35651157259469 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(706491871/2500000000 : ℝ), (-1270980421/2500000000 : ℝ), (433903287/1000000000 : ℝ)] ![(1311928114693/6250000000000 : ℝ), (10839498223259/25000000000000 : ℝ), (35651157259469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(706491871/2500000000 : ℝ)|^21 ≤ (1311928114693/6250000000000 : ℝ)^17
        have hw : |(706491871/2500000000 : ℝ)|=(706491871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1270980421/2500000000 : ℝ)|^21 ≤ (10839498223259/25000000000000 : ℝ)^17
        have hw : |(-1270980421/2500000000 : ℝ)|=(1270980421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433903287/1000000000 : ℝ)|^21 ≤ (35651157259469/100000000000000 : ℝ)^17
        have hw : |(433903287/1000000000 : ℝ)|=(433903287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s0_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (707504911/1000000000 : ℝ)*x 0 + (-2461541653/10000000000 : ℝ)*x 1 + (-478352897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707504911/1000000000 : ℝ)^21 ≤ (32609315954091/50000000000000 : ℝ)^17 := by
    have hnat : (707504911 : ℕ)^21*50000000000000^17 ≤ 32609315954091^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707504911 1000000000 32609315954091 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2461541653/10000000000 : ℝ)^21 ≤ (1106220848439/6250000000000 : ℝ)^17 := by
    have hnat : (2461541653 : ℕ)^21*6250000000000^17 ≤ 1106220848439^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461541653 10000000000 1106220848439 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478352897/2000000000 : ℝ)^21 ≤ (266903664141/1562500000000 : ℝ)^17 := by
    have hnat : (478352897 : ℕ)^21*1562500000000^17 ≤ 266903664141^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478352897 2000000000 266903664141 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(707504911/1000000000 : ℝ), (-2461541653/10000000000 : ℝ), (-478352897/2000000000 : ℝ)] ![(32609315954091/50000000000000 : ℝ), (1106220848439/6250000000000 : ℝ), (266903664141/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(707504911/1000000000 : ℝ)|^21 ≤ (32609315954091/50000000000000 : ℝ)^17
        have hw : |(707504911/1000000000 : ℝ)|=(707504911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2461541653/10000000000 : ℝ)|^21 ≤ (1106220848439/6250000000000 : ℝ)^17
        have hw : |(-2461541653/10000000000 : ℝ)|=(2461541653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478352897/2000000000 : ℝ)|^21 ≤ (266903664141/1562500000000 : ℝ)^17
        have hw : |(-478352897/2000000000 : ℝ)|=(478352897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-92719559/1000000000 : ℝ)*x 0 + (-1093514349/2000000000 : ℝ)*x 1 + (-5451840393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92719559/1000000000 : ℝ)^21 ≤ (662312369621/12500000000000 : ℝ)^17 := by
    have hnat : (92719559 : ℕ)^21*12500000000000^17 ≤ 662312369621^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92719559 1000000000 662312369621 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093514349/2000000000 : ℝ)^21 ≤ (47435018743757/100000000000000 : ℝ)^17 := by
    have hnat : (1093514349 : ℕ)^21*100000000000000^17 ≤ 47435018743757^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093514349 2000000000 47435018743757 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451840393/10000000000 : ℝ)^21 ≤ (47266482283349/100000000000000 : ℝ)^17 := by
    have hnat : (5451840393 : ℕ)^21*100000000000000^17 ≤ 47266482283349^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451840393 10000000000 47266482283349 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92719559/1000000000 : ℝ), (-1093514349/2000000000 : ℝ), (-5451840393/10000000000 : ℝ)] ![(662312369621/12500000000000 : ℝ), (47435018743757/100000000000000 : ℝ), (47266482283349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92719559/1000000000 : ℝ)|^21 ≤ (662312369621/12500000000000 : ℝ)^17
        have hw : |(-92719559/1000000000 : ℝ)|=(92719559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093514349/2000000000 : ℝ)|^21 ≤ (47435018743757/100000000000000 : ℝ)^17
        have hw : |(-1093514349/2000000000 : ℝ)|=(1093514349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5451840393/10000000000 : ℝ)|^21 ≤ (47266482283349/100000000000000 : ℝ)^17
        have hw : |(-5451840393/10000000000 : ℝ)|=(5451840393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (677545109/1250000000 : ℝ)*x 0 + (3411584767/10000000000 : ℝ)*x 1 + (-3421244343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677545109/1250000000 : ℝ)^21 ≤ (46929572918787/100000000000000 : ℝ)^17 := by
    have hnat : (677545109 : ℕ)^21*100000000000000^17 ≤ 46929572918787^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677545109 1250000000 46929572918787 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3411584767/10000000000 : ℝ)^21 ≤ (26488874144913/100000000000000 : ℝ)^17 := by
    have hnat : (3411584767 : ℕ)^21*100000000000000^17 ≤ 26488874144913^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411584767 10000000000 26488874144913 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3421244343/10000000000 : ℝ)^21 ≤ (26581552924953/100000000000000 : ℝ)^17 := by
    have hnat : (3421244343 : ℕ)^21*100000000000000^17 ≤ 26581552924953^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3421244343 10000000000 26581552924953 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677545109/1250000000 : ℝ), (3411584767/10000000000 : ℝ), (-3421244343/10000000000 : ℝ)] ![(46929572918787/100000000000000 : ℝ), (26488874144913/100000000000000 : ℝ), (26581552924953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677545109/1250000000 : ℝ)|^21 ≤ (46929572918787/100000000000000 : ℝ)^17
        have hw : |(677545109/1250000000 : ℝ)|=(677545109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3411584767/10000000000 : ℝ)|^21 ≤ (26488874144913/100000000000000 : ℝ)^17
        have hw : |(3411584767/10000000000 : ℝ)|=(3411584767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3421244343/10000000000 : ℝ)|^21 ≤ (26581552924953/100000000000000 : ℝ)^17
        have hw : |(-3421244343/10000000000 : ℝ)|=(3421244343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5403575599/10000000000 : ℝ)*x 0 + (-427615073/1250000000 : ℝ)*x 1 + (3430606593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403575599/10000000000 : ℝ)^21 ≤ (46750116578261/100000000000000 : ℝ)^17 := by
    have hnat : (5403575599 : ℕ)^21*100000000000000^17 ≤ 46750116578261^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403575599 10000000000 46750116578261 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427615073/1250000000 : ℝ)^21 ≤ (26578445621661/100000000000000 : ℝ)^17 := by
    have hnat : (427615073 : ℕ)^21*100000000000000^17 ≤ 26578445621661^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427615073 1250000000 26578445621661 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3430606593/10000000000 : ℝ)^21 ≤ (1066857511527/4000000000000 : ℝ)^17 := by
    have hnat : (3430606593 : ℕ)^21*4000000000000^17 ≤ 1066857511527^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3430606593 10000000000 1066857511527 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403575599/10000000000 : ℝ), (-427615073/1250000000 : ℝ), (3430606593/10000000000 : ℝ)] ![(46750116578261/100000000000000 : ℝ), (26578445621661/100000000000000 : ℝ), (1066857511527/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403575599/10000000000 : ℝ)|^21 ≤ (46750116578261/100000000000000 : ℝ)^17
        have hw : |(5403575599/10000000000 : ℝ)|=(5403575599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427615073/1250000000 : ℝ)|^21 ≤ (26578445621661/100000000000000 : ℝ)^17
        have hw : |(-427615073/1250000000 : ℝ)|=(427615073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3430606593/10000000000 : ℝ)|^21 ≤ (1066857511527/4000000000000 : ℝ)^17
        have hw : |(3430606593/10000000000 : ℝ)|=(3430606593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322036_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1027875623/2000000000 : ℝ)*x 0 + (-3576384169/10000000000 : ℝ)*x 1 + (-44576177/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027875623/2000000000 : ℝ)^21 ≤ (439429823619/1000000000000 : ℝ)^17 := by
    have hnat : (1027875623 : ℕ)^21*1000000000000^17 ≤ 439429823619^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027875623 2000000000 439429823619 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3576384169/10000000000 : ℝ)^21 ≤ (28078390024209/100000000000000 : ℝ)^17 := by
    have hnat : (3576384169 : ℕ)^21*100000000000000^17 ≤ 28078390024209^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576384169 10000000000 28078390024209 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44576177/125000000 : ℝ)^21 ≤ (5595725518479/20000000000000 : ℝ)^17 := by
    have hnat : (44576177 : ℕ)^21*20000000000000^17 ≤ 5595725518479^17*125000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44576177 125000000 5595725518479 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027875623/2000000000 : ℝ), (-3576384169/10000000000 : ℝ), (-44576177/125000000 : ℝ)] ![(439429823619/1000000000000 : ℝ), (28078390024209/100000000000000 : ℝ), (5595725518479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027875623/2000000000 : ℝ)|^21 ≤ (439429823619/1000000000000 : ℝ)^17
        have hw : |(1027875623/2000000000 : ℝ)|=(1027875623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3576384169/10000000000 : ℝ)|^21 ≤ (28078390024209/100000000000000 : ℝ)^17
        have hw : |(-3576384169/10000000000 : ℝ)|=(3576384169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44576177/125000000 : ℝ)|^21 ≤ (5595725518479/20000000000000 : ℝ)^17
        have hw : |(-44576177/125000000 : ℝ)|=(44576177/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322036 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (167697/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((144209/10000000000 : ℝ)*X 0 0+(-2852848357/5000000000 : ℝ)*X 0 1+(-5705696713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2897425721/5000000000 : ℝ)*X 1 0+(3204449043/10000000000 : ℝ)*X 1 1+(-801112261/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((72435643/125000000 : ℝ)*X 2 0+(-801112261/2500000000 : ℝ)*X 2 1+(1602224523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((7795851/5000000000 : ℝ)*X 0 0+(-6908276663/10000000000 : ℝ)*X 0 1+(-4436307493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((971603141/2500000000 : ℝ)*X 1 0+(6115501741/10000000000 : ℝ)*X 1 1+(-2084320783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5081492499/10000000000 : ℝ)*X 2 0+(-145977633/2000000000 : ℝ)*X 2 1+(5956148543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2778558221/5000000000 : ℝ)*X 0 0+(-1123272047/5000000000 : ℝ)*X 0 1+(-1088264101/2500000000 : ℝ)*X 0 2+(2778558221/5000000000 : ℝ)*X 1 0+(-1123272047/5000000000 : ℝ)*X 1 1+(-1088264101/2500000000 : ℝ)*X 1 2+(2778558221/5000000000 : ℝ)*X 2 0+(-1123272047/5000000000 : ℝ)*X 2 1+(-1088264101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1055669/5000000000 : ℝ)*X 0 0+(-890340591/2000000000 : ℝ)*X 0 1+(-3448575751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((34276339/156250000 : ℝ)*X 1 0+(3716959173/10000000000 : ℝ)*X 1 1+(-1236304763/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4024833591/5000000000 : ℝ)*X 2 0+(-114367479/1000000000 : ℝ)*X 2 1+(146369111/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((9999999999/10000000000 : ℝ)*X 1 0+(41/10000000000 : ℝ)*X 1 1+(41/10000000000 : ℝ)*X 1 2+(9999999999/10000000000 : ℝ)*X 2 0+(41/10000000000 : ℝ)*X 2 1+(41/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7189823787/10000000000 : ℝ)*X 0 0+(-914627913/5000000000 : ℝ)*X 0 1+(-2849419527/10000000000 : ℝ)*X 0 2+(7189823787/10000000000 : ℝ)*X 1 0+(-914627913/5000000000 : ℝ)*X 1 1+(-2849419527/10000000000 : ℝ)*X 1 2+(7189823787/10000000000 : ℝ)*X 2 0+(-914627913/5000000000 : ℝ)*X 2 1+(-2849419527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((4380871/10000000000 : ℝ)*X 0 0+(-7249916381/10000000000 : ℝ)*X 0 1+(-4053636317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3820729767/5000000000 : ℝ)*X 1 0+(3122137357/10000000000 : ℝ)*X 1 1+(-32675261/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((706491871/2500000000 : ℝ)*X 2 0+(-1270980421/2500000000 : ℝ)*X 2 1+(433903287/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((707504911/1000000000 : ℝ)*X 0 0+(-2461541653/10000000000 : ℝ)*X 0 1+(-478352897/2000000000 : ℝ)*X 0 2+(707504911/1000000000 : ℝ)*X 1 0+(-2461541653/10000000000 : ℝ)*X 1 1+(-478352897/2000000000 : ℝ)*X 1 2+(707504911/1000000000 : ℝ)*X 2 0+(-2461541653/10000000000 : ℝ)*X 2 1+(-478352897/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((7991/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7991/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4144404615115182996231/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7286787/1000000000000 : ℝ)*(base1) + (245397036401/500000000000 : ℝ)*(base7) + (408181/200000000000 : ℝ)*(base25) + (485508080293/1000000000000 : ℝ)*(base39) + (54674969701/200000000000 : ℝ)*(base50) + (1728846369469/1000000000000 : ℝ)*(major_s0_0) + (1728846369469/1000000000000 : ℝ)*(major_s0_1) + (1728846369469/1000000000000 : ℝ)*(major_s0_2) + (17310747/1000000000000 : ℝ)*(sp_s0_0) + (2287510894439/1000000000000 : ℝ)*(sp_s0_7) + (2287520918399/1000000000000 : ℝ)*(sp_s0_8) + (2287513781307/1000000000000 : ℝ)*(sp_s0_9) + (1386608522617/1000000000000 : ℝ)*(sp_s0_13) + (1274047/250000000000 : ℝ)*(sp_s0_23) + (447910868301/500000000000 : ℝ)*(f.failure) + (2287520918399/1000000000000 : ℝ)*(f.sum) + (65538376667923/1250000000000000000000000000 : ℝ)*base63 + (826001723629763/2000000000000000000000000000 : ℝ)*base64 + (571169945029763/2000000000000000000000000000 : ℝ)*base66 + (636483441042923/2500000000000000000000000000 : ℝ)*base69 + (2889463822022877/10000000000000000000000000000 : ℝ)*base71 + (382955856770237/2000000000000000000000000000 : ℝ)*base72 + (247242096207077/2500000000000000000000000000 : ℝ)*base74 + (39721560207077/2500000000000000000000000000 : ℝ)*base76 + (2441695993/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (4001/5000000000000000 : ℝ)*base86 + (4001/5000000000000000 : ℝ)*base88 + (4001/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-62549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-62549/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20055669121867705415583/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602523564007/500000000000 : ℝ)*(base7) + (90355562303/500000000000 : ℝ)*(base40) + (6873953/1000000000000 : ℝ)*(base53) + (803514470063/500000000000 : ℝ)*(major_s0_0) + (321397526347/200000000000 : ℝ)*(major_s0_1) + (803490378891/500000000000 : ℝ)*(major_s0_2) + (56441/20000000000 : ℝ)*(sp_s0_0) + (8761363/250000000000 : ℝ)*(sp_s0_1) + (9963681/1000000000000 : ℝ)*(sp_s0_9) + (68306868103/40000000000 : ℝ)*(sp_s0_14) + (1707639479173/1000000000000 : ℝ)*(sp_s0_15) + (1707671434897/1000000000000 : ℝ)*(sp_s0_16) + (41308391/1000000000000 : ℝ)*(sp_s0_17) + (1018863175317/500000000000 : ℝ)*(sp_s0_20) + (41633961131/50000000000 : ℝ)*(f.failure) + (853840699289/500000000000 : ℝ)*(f.sum) + (516305100778139/2500000000000000000000000000 : ℝ)*base63 + (176439966679957/1000000000000000000000000000 : ℝ)*base64 + (24739986280331/400000000000000000000000000 : ℝ)*base67 + (573840453662197/1250000000000000000000000000 : ℝ)*base69 + (108016337635099/5000000000000000000000000000 : ℝ)*base71 + (188733200712401/1000000000000000000000000000 : ℝ)*base73 + (120277806640749/500000000000000000000000000 : ℝ)*base75 + (102666598616279/1250000000000000000000000000 : ℝ)*base76 + (549464498373543/2000000000000000000000000000 : ℝ)*base78 + (331/500000000000000 : ℝ)*base86 + (331/500000000000000 : ℝ)*base88 + (331/500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-32083/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-32083/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80116182275285180891781/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38871964857/31250000000 : ℝ)*(base7) + (33285097893/100000000000 : ℝ)*(base39) + (1871157/250000000000 : ℝ)*(base43) + (224958553/10000000000 : ℝ)*(base50) + (1839143298931/1000000000000 : ℝ)*(major_s0_0) + (919552459671/500000000000 : ℝ)*(major_s0_1) + (183911240397/100000000000 : ℝ)*(major_s0_2) + (31770739/1000000000000 : ℝ)*(sp_s0_2) + (13630757/1000000000000 : ℝ)*(sp_s0_7) + (386187/12500000000 : ℝ)*(sp_s0_17) + (2029911725773/1000000000000 : ℝ)*(sp_s0_21) + (2029932841159/1000000000000 : ℝ)*(sp_s0_22) + (2029893585791/1000000000000 : ℝ)*(sp_s0_23) + (137303764549/62500000000 : ℝ)*(sp_s0_27) + (952957357361/1000000000000 : ℝ)*(f.failure) + (2029932841159/1000000000000 : ℝ)*(f.sum) + (25939767929061/39062500000000000000000000 : ℝ)*base63 + (54400399644019/200000000000000000000000000 : ℝ)*base64 + (605199727896983/1000000000000000000000000000 : ℝ)*base67 + (150374757157099/250000000000000000000000000 : ℝ)*base69 + (736668878920721/5000000000000000000000000000 : ℝ)*base70 + (941749962577037/2000000000000000000000000000 : ℝ)*base73 + (1779103846319457/1250000000000000000000000000 : ℝ)*base75 + (567615524160123/2500000000000000000000000000 : ℝ)*base76 + (1004981594171003/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (61/10000000000000000 : ℝ)*base86 + (9939/10000000000000000 : ℝ)*base89 + (9939/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (7991/25000 : ℝ) ^ (41/8 : ℝ) ≤ (144663262271718497/50000000000000000000 : ℝ) := by
    have hpowers : (7991/25000 : ℝ)^41 ≤ (144663262271718497/50000000000000000000 : ℝ)^8 := by
      have hnat : (7991 : ℕ)^41*50000000000000000000^8 ≤ 144663262271718497^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7991 25000 144663262271718497 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7991/25000 : ℝ)) (X := (144663262271718497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50144663262271718497/50000000000000000000 : ℝ) ≤ (10005638833730701/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50144663262271718497/50000000000000000000 : ℝ)^8 ≤ (10005638833730701/10000000000000000 : ℝ)^41 := by
      have hnat : (50144663262271718497 : ℕ)^8*10000000000000000^41 ≤ 10005638833730701^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50144663262271718497 50000000000000000000 10005638833730701 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005638833730701/10000000000000000 : ℝ)) (X := (50144663262271718497/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25144663262271718497/25000000000000000000 : ℝ) ≤ (10011264589211509/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25144663262271718497/25000000000000000000 : ℝ)^8 ≤ (10011264589211509/10000000000000000 : ℝ)^41 := by
      have hnat : (25144663262271718497 : ℕ)^8*10000000000000000^41 ≤ 10011264589211509^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25144663262271718497 25000000000000000000 10011264589211509 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011264589211509/10000000000000000 : ℝ)) (X := (25144663262271718497/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5638833730701/3196400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(703219435101/399550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (7991/25000 : ℝ)) (alpha := (5638833730701/3196400000000000 : ℝ)) (beta := (703219435101/399550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7991/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5638833730701/3196400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(703219435101/399550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62549/100000 : ℝ) ^ (41/8 : ℝ) ≤ (564299178175354573/6250000000000000000 : ℝ) := by
    have hpowers : (62549/100000 : ℝ)^41 ≤ (564299178175354573/6250000000000000000 : ℝ)^8 := by
      have hnat : (62549 : ℕ)^41*6250000000000000000^8 ≤ 564299178175354573^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62549 100000 564299178175354573 6250000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62549/100000 : ℝ)) (X := (564299178175354573/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (6814299178175354573/6250000000000000000 : ℝ) ≤ (317815540841829/312500000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (6814299178175354573/6250000000000000000 : ℝ)^8 ≤ (317815540841829/312500000000000 : ℝ)^41 := by
      have hnat : (6814299178175354573 : ℕ)^8*312500000000000^41 ≤ 317815540841829^41*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6814299178175354573 6250000000000000000 317815540841829 312500000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (317815540841829/312500000000000 : ℝ)) (X := (6814299178175354573/6250000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3689299178175354573/3125000000000000000 : ℝ) ≤ (10329209674895403/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3689299178175354573/3125000000000000000 : ℝ)^8 ≤ (10329209674895403/10000000000000000 : ℝ)^41 := by
      have hnat : (3689299178175354573 : ℕ)^8*10000000000000000^41 ≤ 10329209674895403^41*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689299178175354573 3125000000000000000 10329209674895403 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10329209674895403/10000000000000000 : ℝ)) (X := (3689299178175354573/3125000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5315540841829/195465625000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(254579788731/10007840000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (62549/100000 : ℝ)) (alpha := (5315540841829/195465625000000 : ℝ)) (beta := (254579788731/10007840000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (62549/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5315540841829/195465625000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(254579788731/10007840000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (32083/50000 : ℝ) ^ (41/8 : ℝ) ≤ (5145267517908151163/50000000000000000000 : ℝ) := by
    have hpowers : (32083/50000 : ℝ)^41 ≤ (5145267517908151163/50000000000000000000 : ℝ)^8 := by
      have hnat : (32083 : ℕ)^41*50000000000000000000^8 ≤ 5145267517908151163^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32083 50000 5145267517908151163 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32083/50000 : ℝ)) (X := (5145267517908151163/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (55145267517908151163/50000000000000000000 : ℝ) ≤ (318529871765221/312500000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (55145267517908151163/50000000000000000000 : ℝ)^8 ≤ (318529871765221/312500000000000 : ℝ)^41 := by
      have hnat : (55145267517908151163 : ℕ)^8*312500000000000^41 ≤ 318529871765221^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55145267517908151163 50000000000000000000 318529871765221 312500000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (318529871765221/312500000000000 : ℝ)) (X := (55145267517908151163/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (30145267517908151163/25000000000000000000 : ℝ) ≤ (1296490551688209/1250000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (30145267517908151163/25000000000000000000 : ℝ)^8 ≤ (1296490551688209/1250000000000000 : ℝ)^41 := by
      have hnat : (30145267517908151163 : ℕ)^8*1250000000000000^41 ≤ 1296490551688209^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30145267517908151163 25000000000000000000 1296490551688209 1250000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1296490551688209/1250000000000000 : ℝ)) (X := (30145267517908151163/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6029871765221/200518750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(894842585093/32083000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (32083/50000 : ℝ)) (alpha := (6029871765221/200518750000000 : ℝ)) (beta := (894842585093/32083000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (32083/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6029871765221/200518750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(894842585093/32083000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-92719559/1000000000 : ℝ)*X 0 0+(-1093514349/2000000000 : ℝ)*X 0 1+(-5451840393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((677545109/1250000000 : ℝ)*X 1 0+(3411584767/10000000000 : ℝ)*X 1 1+(-3421244343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5403575599/10000000000 : ℝ)*X 2 0+(-427615073/1250000000 : ℝ)*X 2 1+(3430606593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1027875623/2000000000 : ℝ)*X 0 0+(-3576384169/10000000000 : ℝ)*X 0 1+(-44576177/125000000 : ℝ)*X 0 2+(1027875623/2000000000 : ℝ)*X 1 0+(-3576384169/10000000000 : ℝ)*X 1 1+(-44576177/125000000 : ℝ)*X 1 2+(1027875623/2000000000 : ℝ)*X 2 0+(-3576384169/10000000000 : ℝ)*X 2 1+(-44576177/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322036_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-684882515766688027081746520813564299/80180078499485000000000000000000000 : ℝ) := by norm_num
    linear_combination (24747/250000000000 : ℝ)*(base7) + (2351/25000000000 : ℝ)*(base10) + (20141/1000000000000 : ℝ)*(base25) + (238120633607/200000000000 : ℝ)*(base39) + (743536539/1250000000 : ℝ)*(base40) + (8762303451/125000000000 : ℝ)*(base50) + (433281967/6250000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299000029/10000000000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (2847267846983/1000000000000 : ℝ)*(sp_s1_0) + (2847267938123/1000000000000 : ℝ)*(sp_s1_1) + (1423633960441/500000000000 : ℝ)*(sp_s1_2) + (250000024747/250000000000 : ℝ)*(sp_s1_6) + (2847267938123/1000000000000 : ℝ)*(f.sum) + (641408704442812359/2006759567000000000000000000000 : ℝ)*base62 + (76525406377481/320830000000000000000000000 : ℝ)*base65 + (97739915869301/625490000000000000000000000 : ℝ)*base67 + (39399040803677/80207500000000000000000000 : ℝ)*base68 + (169782723824528643/2563752530000000000000000000000 : ℝ)*base71 + (35716082332421/79910000000000000000000000 : ℝ)*base72 + (60717435321421/312745000000000000000000000 : ℝ)*base74 + (1865912288773/3995500000000000000000000 : ℝ)*base77 + (289825335407238879/312393161875000000000000000000 : ℝ)*base78 + (29/10000000000 : ℝ)*base81 + (29/10000000000 : ℝ)*base85 + (29/10000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p022_b018 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=36 := by omega
  rcases hc with rfl
  · exact collision_c322036 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
