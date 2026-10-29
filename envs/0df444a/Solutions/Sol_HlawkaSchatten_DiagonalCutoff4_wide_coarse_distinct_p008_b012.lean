-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b012
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:00.638012+00:00
-- url     : https://prove2.me/submissions/ae5d795c-06af-4b0d-8d79-c29591d20652

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
theorem collision_support_c308021_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-499217739/1250000000 : ℝ)*x 0 + (774747263/2000000000 : ℝ)*x 1 + (992551821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499217739/1250000000 : ℝ)^35 ≤ (7606946709897/25000000000000 : ℝ)^27 := by
    have hnat : (499217739 : ℕ)^35*25000000000000^27 ≤ 7606946709897^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499217739 1250000000 7606946709897 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774747263/2000000000 : ℝ)^35 ≤ (14623944159277/50000000000000 : ℝ)^27 := by
    have hnat : (774747263 : ℕ)^35*50000000000000^27 ≤ 14623944159277^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774747263 2000000000 14623944159277 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992551821/2000000000 : ℝ)^35 ≤ (4032432481901/10000000000000 : ℝ)^27 := by
    have hnat : (992551821 : ℕ)^35*10000000000000^27 ≤ 4032432481901^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992551821 2000000000 4032432481901 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499217739/1250000000 : ℝ), (774747263/2000000000 : ℝ), (992551821/2000000000 : ℝ)] ![(7606946709897/25000000000000 : ℝ), (14623944159277/50000000000000 : ℝ), (4032432481901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499217739/1250000000 : ℝ)|^35 ≤ (7606946709897/25000000000000 : ℝ)^27
        have hw : |(-499217739/1250000000 : ℝ)|=(499217739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(774747263/2000000000 : ℝ)|^35 ≤ (14623944159277/50000000000000 : ℝ)^27
        have hw : |(774747263/2000000000 : ℝ)|=(774747263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(992551821/2000000000 : ℝ)|^35 ≤ (4032432481901/10000000000000 : ℝ)^27
        have hw : |(992551821/2000000000 : ℝ)|=(992551821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6134044551/10000000000 : ℝ)*x 0 + (-1025191737/10000000000 : ℝ)*x 1 + (2546834373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6134044551/10000000000 : ℝ)^35 ≤ (53070982303599/100000000000000 : ℝ)^27 := by
    have hnat : (6134044551 : ℕ)^35*100000000000000^27 ≤ 53070982303599^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134044551 10000000000 53070982303599 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025191737/10000000000 : ℝ)^35 ≤ (2610239247547/50000000000000 : ℝ)^27 := by
    have hnat : (1025191737 : ℕ)^35*50000000000000^27 ≤ 2610239247547^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025191737 10000000000 2610239247547 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2546834373/5000000000 : ℝ)^35 ≤ (41708539188983/100000000000000 : ℝ)^27 := by
    have hnat : (2546834373 : ℕ)^35*100000000000000^27 ≤ 41708539188983^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546834373 5000000000 41708539188983 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6134044551/10000000000 : ℝ), (-1025191737/10000000000 : ℝ), (2546834373/5000000000 : ℝ)] ![(53070982303599/100000000000000 : ℝ), (2610239247547/50000000000000 : ℝ), (41708539188983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6134044551/10000000000 : ℝ)|^35 ≤ (53070982303599/100000000000000 : ℝ)^27
        have hw : |(6134044551/10000000000 : ℝ)|=(6134044551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025191737/10000000000 : ℝ)|^35 ≤ (2610239247547/50000000000000 : ℝ)^27
        have hw : |(-1025191737/10000000000 : ℝ)|=(1025191737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2546834373/5000000000 : ℝ)|^35 ≤ (41708539188983/100000000000000 : ℝ)^27
        have hw : |(2546834373/5000000000 : ℝ)|=(2546834373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (47813099/250000000 : ℝ)*x 0 + (782450233/1000000000 : ℝ)*x 1 + (-475313423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47813099/250000000 : ℝ)^35 ≤ (5857599435169/50000000000000 : ℝ)^27 := by
    have hnat : (47813099 : ℕ)^35*50000000000000^27 ≤ 5857599435169^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47813099 250000000 5857599435169 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782450233/1000000000 : ℝ)^35 ≤ (72759272194703/100000000000000 : ℝ)^27 := by
    have hnat : (782450233 : ℕ)^35*100000000000000^27 ≤ 72759272194703^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782450233 1000000000 72759272194703 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475313423/2000000000 : ℝ)^35 ≤ (621021156639/4000000000000 : ℝ)^27 := by
    have hnat : (475313423 : ℕ)^35*4000000000000^27 ≤ 621021156639^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475313423 2000000000 621021156639 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(47813099/250000000 : ℝ), (782450233/1000000000 : ℝ), (-475313423/2000000000 : ℝ)] ![(5857599435169/50000000000000 : ℝ), (72759272194703/100000000000000 : ℝ), (621021156639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(47813099/250000000 : ℝ)|^35 ≤ (5857599435169/50000000000000 : ℝ)^27
        have hw : |(47813099/250000000 : ℝ)|=(47813099/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(782450233/1000000000 : ℝ)|^35 ≤ (72759272194703/100000000000000 : ℝ)^27
        have hw : |(782450233/1000000000 : ℝ)|=(782450233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475313423/2000000000 : ℝ)|^35 ≤ (621021156639/4000000000000 : ℝ)^27
        have hw : |(-475313423/2000000000 : ℝ)|=(475313423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4185464381/10000000000 : ℝ)*x 0 + (2850384197/10000000000 : ℝ)*x 1 + (5678034701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185464381/10000000000 : ℝ)^35 ≤ (2020913440447/6250000000000 : ℝ)^27 := by
    have hnat : (4185464381 : ℕ)^35*6250000000000^27 ≤ 2020913440447^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185464381 10000000000 2020913440447 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850384197/10000000000 : ℝ)^35 ≤ (19651391067623/100000000000000 : ℝ)^27 := by
    have hnat : (2850384197 : ℕ)^35*100000000000000^27 ≤ 19651391067623^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850384197 10000000000 19651391067623 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5678034701/10000000000 : ℝ)^35 ≤ (9602798774261/20000000000000 : ℝ)^27 := by
    have hnat : (5678034701 : ℕ)^35*20000000000000^27 ≤ 9602798774261^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678034701 10000000000 9602798774261 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4185464381/10000000000 : ℝ), (2850384197/10000000000 : ℝ), (5678034701/10000000000 : ℝ)] ![(2020913440447/6250000000000 : ℝ), (19651391067623/100000000000000 : ℝ), (9602798774261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4185464381/10000000000 : ℝ)|^35 ≤ (2020913440447/6250000000000 : ℝ)^27
        have hw : |(-4185464381/10000000000 : ℝ)|=(4185464381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850384197/10000000000 : ℝ)|^35 ≤ (19651391067623/100000000000000 : ℝ)^27
        have hw : |(2850384197/10000000000 : ℝ)|=(2850384197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5678034701/10000000000 : ℝ)|^35 ≤ (9602798774261/20000000000000 : ℝ)^27
        have hw : |(5678034701/10000000000 : ℝ)|=(5678034701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5506153001/10000000000 : ℝ)*x 0 + (-257235259/10000000000 : ℝ)*x 1 + (1531750243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506153001/10000000000 : ℝ)^35 ≤ (4613840520049/10000000000000 : ℝ)^27 := by
    have hnat : (5506153001 : ℕ)^35*10000000000000^27 ≤ 4613840520049^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506153001 10000000000 4613840520049 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257235259/10000000000 : ℝ)^35 ≤ (8695955537/1000000000000 : ℝ)^27 := by
    have hnat : (257235259 : ℕ)^35*1000000000000^27 ≤ 8695955537^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257235259 10000000000 8695955537 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1531750243/2500000000 : ℝ)^35 ≤ (52991999241993/100000000000000 : ℝ)^27 := by
    have hnat : (1531750243 : ℕ)^35*100000000000000^27 ≤ 52991999241993^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531750243 2500000000 52991999241993 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506153001/10000000000 : ℝ), (-257235259/10000000000 : ℝ), (1531750243/2500000000 : ℝ)] ![(4613840520049/10000000000000 : ℝ), (8695955537/1000000000000 : ℝ), (52991999241993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506153001/10000000000 : ℝ)|^35 ≤ (4613840520049/10000000000000 : ℝ)^27
        have hw : |(5506153001/10000000000 : ℝ)|=(5506153001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257235259/10000000000 : ℝ)|^35 ≤ (8695955537/1000000000000 : ℝ)^27
        have hw : |(-257235259/10000000000 : ℝ)|=(257235259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1531750243/2500000000 : ℝ)|^35 ≤ (52991999241993/100000000000000 : ℝ)^27
        have hw : |(1531750243/2500000000 : ℝ)|=(1531750243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (589338343/10000000000 : ℝ)*x 0 + (4754066019/5000000000 : ℝ)*x 1 + (-99937643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589338343/10000000000 : ℝ)^35 ≤ (2546996286821/100000000000000 : ℝ)^27 := by
    have hnat : (589338343 : ℕ)^35*100000000000000^27 ≤ 2546996286821^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589338343 10000000000 2546996286821 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4754066019/5000000000 : ℝ)^35 ≤ (93670943391607/100000000000000 : ℝ)^27 := by
    have hnat : (4754066019 : ℕ)^35*100000000000000^27 ≤ 93670943391607^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754066019 5000000000 93670943391607 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99937643/1250000000 : ℝ)^35 ≤ (15128241219/400000000000 : ℝ)^27 := by
    have hnat : (99937643 : ℕ)^35*400000000000^27 ≤ 15128241219^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99937643 1250000000 15128241219 400000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(589338343/10000000000 : ℝ), (4754066019/5000000000 : ℝ), (-99937643/1250000000 : ℝ)] ![(2546996286821/100000000000000 : ℝ), (93670943391607/100000000000000 : ℝ), (15128241219/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(589338343/10000000000 : ℝ)|^35 ≤ (2546996286821/100000000000000 : ℝ)^27
        have hw : |(589338343/10000000000 : ℝ)|=(589338343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4754066019/5000000000 : ℝ)|^35 ≤ (93670943391607/100000000000000 : ℝ)^27
        have hw : |(4754066019/5000000000 : ℝ)|=(4754066019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99937643/1250000000 : ℝ)|^35 ≤ (15128241219/400000000000 : ℝ)^27
        have hw : |(-99937643/1250000000 : ℝ)|=(99937643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (798260899/2000000000 : ℝ)*x 0 + (883482261/2000000000 : ℝ)*x 1 + (2220672629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798260899/2000000000 : ℝ)^35 ≤ (15201858167053/50000000000000 : ℝ)^27 := by
    have hnat : (798260899 : ℕ)^35*50000000000000^27 ≤ 15201858167053^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798260899 2000000000 15201858167053 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883482261/2000000000 : ℝ)^35 ≤ (3467627056841/10000000000000 : ℝ)^27 := by
    have hnat : (883482261 : ℕ)^35*10000000000000^27 ≤ 3467627056841^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883482261 2000000000 3467627056841 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220672629/5000000000 : ℝ)^35 ≤ (17460006538629/50000000000000 : ℝ)^27 := by
    have hnat : (2220672629 : ℕ)^35*50000000000000^27 ≤ 17460006538629^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220672629 5000000000 17460006538629 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(798260899/2000000000 : ℝ), (883482261/2000000000 : ℝ), (2220672629/5000000000 : ℝ)] ![(15201858167053/50000000000000 : ℝ), (3467627056841/10000000000000 : ℝ), (17460006538629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(798260899/2000000000 : ℝ)|^35 ≤ (15201858167053/50000000000000 : ℝ)^27
        have hw : |(798260899/2000000000 : ℝ)|=(798260899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883482261/2000000000 : ℝ)|^35 ≤ (3467627056841/10000000000000 : ℝ)^27
        have hw : |(883482261/2000000000 : ℝ)|=(883482261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220672629/5000000000 : ℝ)|^35 ≤ (17460006538629/50000000000000 : ℝ)^27
        have hw : |(2220672629/5000000000 : ℝ)|=(2220672629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-5178556997/10000000000 : ℝ)*x 0 + (830511871/2500000000 : ℝ)*x 1 + (536703587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178556997/10000000000 : ℝ)^35 ≤ (8522359899551/20000000000000 : ℝ)^27 := by
    have hnat : (5178556997 : ℕ)^35*20000000000000^27 ≤ 8522359899551^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178556997 10000000000 8522359899551 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830511871/2500000000 : ℝ)^35 ≤ (11983126992927/50000000000000 : ℝ)^27 := by
    have hnat : (830511871 : ℕ)^35*50000000000000^27 ≤ 11983126992927^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830511871 2500000000 11983126992927 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536703587/1250000000 : ℝ)^35 ≤ (16710973247619/50000000000000 : ℝ)^27 := by
    have hnat : (536703587 : ℕ)^35*50000000000000^27 ≤ 16710973247619^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536703587 1250000000 16710973247619 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5178556997/10000000000 : ℝ), (830511871/2500000000 : ℝ), (536703587/1250000000 : ℝ)] ![(8522359899551/20000000000000 : ℝ), (11983126992927/50000000000000 : ℝ), (16710973247619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5178556997/10000000000 : ℝ)|^35 ≤ (8522359899551/20000000000000 : ℝ)^27
        have hw : |(-5178556997/10000000000 : ℝ)|=(5178556997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830511871/2500000000 : ℝ)|^35 ≤ (11983126992927/50000000000000 : ℝ)^27
        have hw : |(830511871/2500000000 : ℝ)|=(830511871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(536703587/1250000000 : ℝ)|^35 ≤ (16710973247619/50000000000000 : ℝ)^27
        have hw : |(536703587/1250000000 : ℝ)|=(536703587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (367858341/625000000 : ℝ)*x 0 + (-1078921131/10000000000 : ℝ)*x 1 + (5319313147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367858341/625000000 : ℝ)^35 ≤ (3143933674699/6250000000000 : ℝ)^27 := by
    have hnat : (367858341 : ℕ)^35*6250000000000^27 ≤ 3143933674699^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367858341 625000000 3143933674699 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078921131/10000000000 : ℝ)^35 ≤ (697233332719/12500000000000 : ℝ)^27 := by
    have hnat : (1078921131 : ℕ)^35*12500000000000^27 ≤ 697233332719^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078921131 10000000000 697233332719 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5319313147/10000000000 : ℝ)^35 ≤ (44119194530397/100000000000000 : ℝ)^27 := by
    have hnat : (5319313147 : ℕ)^35*100000000000000^27 ≤ 44119194530397^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5319313147 10000000000 44119194530397 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(367858341/625000000 : ℝ), (-1078921131/10000000000 : ℝ), (5319313147/10000000000 : ℝ)] ![(3143933674699/6250000000000 : ℝ), (697233332719/12500000000000 : ℝ), (44119194530397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(367858341/625000000 : ℝ)|^35 ≤ (3143933674699/6250000000000 : ℝ)^27
        have hw : |(367858341/625000000 : ℝ)|=(367858341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078921131/10000000000 : ℝ)|^35 ≤ (697233332719/12500000000000 : ℝ)^27
        have hw : |(-1078921131/10000000000 : ℝ)|=(1078921131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5319313147/10000000000 : ℝ)|^35 ≤ (44119194530397/100000000000000 : ℝ)^27
        have hw : |(5319313147/10000000000 : ℝ)|=(5319313147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (863470489/10000000000 : ℝ)*x 0 + (8300622477/10000000000 : ℝ)*x 1 + (-2580218827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863470489/10000000000 : ℝ)^35 ≤ (1044724024087/25000000000000 : ℝ)^27 := by
    have hnat : (863470489 : ℕ)^35*25000000000000^27 ≤ 1044724024087^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863470489 10000000000 1044724024087 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8300622477/10000000000 : ℝ)^35 ≤ (785495046787/1000000000000 : ℝ)^27 := by
    have hnat : (8300622477 : ℕ)^35*1000000000000^27 ≤ 785495046787^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8300622477 10000000000 785495046787 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2580218827/10000000000 : ℝ)^35 ≤ (8635799605631/50000000000000 : ℝ)^27 := by
    have hnat : (2580218827 : ℕ)^35*50000000000000^27 ≤ 8635799605631^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580218827 10000000000 8635799605631 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863470489/10000000000 : ℝ), (8300622477/10000000000 : ℝ), (-2580218827/10000000000 : ℝ)] ![(1044724024087/25000000000000 : ℝ), (785495046787/1000000000000 : ℝ), (8635799605631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863470489/10000000000 : ℝ)|^35 ≤ (1044724024087/25000000000000 : ℝ)^27
        have hw : |(863470489/10000000000 : ℝ)|=(863470489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8300622477/10000000000 : ℝ)|^35 ≤ (785495046787/1000000000000 : ℝ)^27
        have hw : |(8300622477/10000000000 : ℝ)|=(8300622477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2580218827/10000000000 : ℝ)|^35 ≤ (8635799605631/50000000000000 : ℝ)^27
        have hw : |(-2580218827/10000000000 : ℝ)|=(2580218827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (526906513/2000000000 : ℝ)*x 0 + (92114527/200000000 : ℝ)*x 1 + (5461239443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526906513/2000000000 : ℝ)^35 ≤ (8872176832363/50000000000000 : ℝ)^27 := by
    have hnat : (526906513 : ℕ)^35*50000000000000^27 ≤ 8872176832363^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526906513 2000000000 8872176832363 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92114527/200000000 : ℝ)^35 ≤ (285972745089/781250000000 : ℝ)^27 := by
    have hnat : (92114527 : ℕ)^35*781250000000^27 ≤ 285972745089^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92114527 200000000 285972745089 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461239443/10000000000 : ℝ)^35 ≤ (22825567473793/50000000000000 : ℝ)^27 := by
    have hnat : (5461239443 : ℕ)^35*50000000000000^27 ≤ 22825567473793^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461239443 10000000000 22825567473793 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526906513/2000000000 : ℝ), (92114527/200000000 : ℝ), (5461239443/10000000000 : ℝ)] ![(8872176832363/50000000000000 : ℝ), (285972745089/781250000000 : ℝ), (22825567473793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526906513/2000000000 : ℝ)|^35 ≤ (8872176832363/50000000000000 : ℝ)^27
        have hw : |(526906513/2000000000 : ℝ)|=(526906513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92114527/200000000 : ℝ)|^35 ≤ (285972745089/781250000000 : ℝ)^27
        have hw : |(92114527/200000000 : ℝ)|=(92114527/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461239443/10000000000 : ℝ)|^35 ≤ (22825567473793/50000000000000 : ℝ)^27
        have hw : |(5461239443/10000000000 : ℝ)|=(5461239443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-596524341/2000000000 : ℝ)*x 0 + (3931019803/10000000000 : ℝ)*x 1 + (2899720187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (596524341/2000000000 : ℝ)^35 ≤ (20841240194013/100000000000000 : ℝ)^27 := by
    have hnat : (596524341 : ℕ)^35*100000000000000^27 ≤ 20841240194013^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596524341 2000000000 20841240194013 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3931019803/10000000000 : ℝ)^35 ≤ (29809770576427/100000000000000 : ℝ)^27 := by
    have hnat : (3931019803 : ℕ)^35*100000000000000^27 ≤ 29809770576427^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3931019803 10000000000 29809770576427 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899720187/5000000000 : ℝ)^35 ≤ (49348989223823/100000000000000 : ℝ)^27 := by
    have hnat : (2899720187 : ℕ)^35*100000000000000^27 ≤ 49348989223823^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899720187 5000000000 49348989223823 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-596524341/2000000000 : ℝ), (3931019803/10000000000 : ℝ), (2899720187/5000000000 : ℝ)] ![(20841240194013/100000000000000 : ℝ), (29809770576427/100000000000000 : ℝ), (49348989223823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-596524341/2000000000 : ℝ)|^35 ≤ (20841240194013/100000000000000 : ℝ)^27
        have hw : |(-596524341/2000000000 : ℝ)|=(596524341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3931019803/10000000000 : ℝ)|^35 ≤ (29809770576427/100000000000000 : ℝ)^27
        have hw : |(3931019803/10000000000 : ℝ)|=(3931019803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2899720187/5000000000 : ℝ)|^35 ≤ (49348989223823/100000000000000 : ℝ)^27
        have hw : |(2899720187/5000000000 : ℝ)|=(2899720187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7886017351/10000000000 : ℝ)*x 0 + (-24151361/1000000000 : ℝ)*x 1 + (3505635293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7886017351/10000000000 : ℝ)^35 ≤ (18375411092701/25000000000000 : ℝ)^27 := by
    have hnat : (7886017351 : ℕ)^35*25000000000000^27 ≤ 18375411092701^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7886017351 10000000000 18375411092701 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24151361/1000000000 : ℝ)^35 ≤ (801333312939/100000000000000 : ℝ)^27 := by
    have hnat : (24151361 : ℕ)^35*100000000000000^27 ≤ 801333312939^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24151361 1000000000 801333312939 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3505635293/10000000000 : ℝ)^35 ≤ (256970222993/1000000000000 : ℝ)^27 := by
    have hnat : (3505635293 : ℕ)^35*1000000000000^27 ≤ 256970222993^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505635293 10000000000 256970222993 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7886017351/10000000000 : ℝ), (-24151361/1000000000 : ℝ), (3505635293/10000000000 : ℝ)] ![(18375411092701/25000000000000 : ℝ), (801333312939/100000000000000 : ℝ), (256970222993/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7886017351/10000000000 : ℝ)|^35 ≤ (18375411092701/25000000000000 : ℝ)^27
        have hw : |(7886017351/10000000000 : ℝ)|=(7886017351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24151361/1000000000 : ℝ)|^35 ≤ (801333312939/100000000000000 : ℝ)^27
        have hw : |(-24151361/1000000000 : ℝ)|=(24151361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3505635293/10000000000 : ℝ)|^35 ≤ (256970222993/1000000000000 : ℝ)^27
        have hw : |(3505635293/10000000000 : ℝ)|=(3505635293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (118166447/2000000000 : ℝ)*x 0 + (466466439/500000000 : ℝ)*x 1 + (-229764057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118166447/2000000000 : ℝ)^35 ≤ (2555368688601/100000000000000 : ℝ)^27 := by
    have hnat : (118166447 : ℕ)^35*100000000000000^27 ≤ 2555368688601^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118166447 2000000000 2555368688601 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466466439/500000000 : ℝ)^35 ≤ (91393894357891/100000000000000 : ℝ)^27 := by
    have hnat : (466466439 : ℕ)^35*100000000000000^27 ≤ 91393894357891^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466466439 500000000 91393894357891 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229764057/2000000000 : ℝ)^35 ≤ (6050736936367/100000000000000 : ℝ)^27 := by
    have hnat : (229764057 : ℕ)^35*100000000000000^27 ≤ 6050736936367^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229764057 2000000000 6050736936367 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(118166447/2000000000 : ℝ), (466466439/500000000 : ℝ), (-229764057/2000000000 : ℝ)] ![(2555368688601/100000000000000 : ℝ), (91393894357891/100000000000000 : ℝ), (6050736936367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(118166447/2000000000 : ℝ)|^35 ≤ (2555368688601/100000000000000 : ℝ)^27
        have hw : |(118166447/2000000000 : ℝ)|=(118166447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(466466439/500000000 : ℝ)|^35 ≤ (91393894357891/100000000000000 : ℝ)^27
        have hw : |(466466439/500000000 : ℝ)|=(466466439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229764057/2000000000 : ℝ)|^35 ≤ (6050736936367/100000000000000 : ℝ)^27
        have hw : |(-229764057/2000000000 : ℝ)|=(229764057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s0_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6885169603/10000000000 : ℝ)*x 0 + (2526257897/10000000000 : ℝ)*x 1 + (3060720321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6885169603/10000000000 : ℝ)^35 ≤ (15410948189213/25000000000000 : ℝ)^27 := by
    have hnat : (6885169603 : ℕ)^35*25000000000000^27 ≤ 15410948189213^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6885169603 10000000000 15410948189213 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2526257897/10000000000 : ℝ)^35 ≤ (16804826576337/100000000000000 : ℝ)^27 := by
    have hnat : (2526257897 : ℕ)^35*100000000000000^27 ≤ 16804826576337^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526257897 10000000000 16804826576337 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3060720321/10000000000 : ℝ)^35 ≤ (5387845165217/25000000000000 : ℝ)^27 := by
    have hnat : (3060720321 : ℕ)^35*25000000000000^27 ≤ 5387845165217^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060720321 10000000000 5387845165217 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6885169603/10000000000 : ℝ), (2526257897/10000000000 : ℝ), (3060720321/10000000000 : ℝ)] ![(15410948189213/25000000000000 : ℝ), (16804826576337/100000000000000 : ℝ), (5387845165217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6885169603/10000000000 : ℝ)|^35 ≤ (15410948189213/25000000000000 : ℝ)^27
        have hw : |(6885169603/10000000000 : ℝ)|=(6885169603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2526257897/10000000000 : ℝ)|^35 ≤ (16804826576337/100000000000000 : ℝ)^27
        have hw : |(2526257897/10000000000 : ℝ)|=(2526257897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3060720321/10000000000 : ℝ)|^35 ≤ (5387845165217/25000000000000 : ℝ)^27
        have hw : |(3060720321/10000000000 : ℝ)|=(3060720321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2034239641/5000000000 : ℝ)*x 0 + (4258777263/10000000000 : ℝ)*x 1 + (282729213/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034239641/5000000000 : ℝ)^35 ≤ (97399855109/312500000000 : ℝ)^27 := by
    have hnat : (2034239641 : ℕ)^35*312500000000^27 ≤ 97399855109^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034239641 5000000000 97399855109 312500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4258777263/10000000000 : ℝ)^35 ≤ (33070702738383/100000000000000 : ℝ)^27 := by
    have hnat : (4258777263 : ℕ)^35*100000000000000^27 ≤ 33070702738383^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258777263 10000000000 33070702738383 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282729213/625000000 : ℝ)^35 ≤ (8940335901809/25000000000000 : ℝ)^27 := by
    have hnat : (282729213 : ℕ)^35*25000000000000^27 ≤ 8940335901809^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282729213 625000000 8940335901809 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2034239641/5000000000 : ℝ), (4258777263/10000000000 : ℝ), (282729213/625000000 : ℝ)] ![(97399855109/312500000000 : ℝ), (33070702738383/100000000000000 : ℝ), (8940335901809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2034239641/5000000000 : ℝ)|^35 ≤ (97399855109/312500000000 : ℝ)^27
        have hw : |(-2034239641/5000000000 : ℝ)|=(2034239641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4258777263/10000000000 : ℝ)|^35 ≤ (33070702738383/100000000000000 : ℝ)^27
        have hw : |(4258777263/10000000000 : ℝ)|=(4258777263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282729213/625000000 : ℝ)|^35 ≤ (8940335901809/25000000000000 : ℝ)^27
        have hw : |(282729213/625000000 : ℝ)|=(282729213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1086544993/2000000000 : ℝ)*x 0 + (-2354423811/10000000000 : ℝ)*x 1 + (1216767561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086544993/2000000000 : ℝ)^35 ≤ (1813695778293/4000000000000 : ℝ)^27 := by
    have hnat : (1086544993 : ℕ)^35*4000000000000^27 ≤ 1813695778293^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086544993 2000000000 1813695778293 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2354423811/10000000000 : ℝ)^35 ≤ (15338270297599/100000000000000 : ℝ)^27 := by
    have hnat : (2354423811 : ℕ)^35*100000000000000^27 ≤ 15338270297599^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354423811 10000000000 15338270297599 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216767561/2500000000 : ℝ)^35 ≤ (4914916903591/12500000000000 : ℝ)^27 := by
    have hnat : (1216767561 : ℕ)^35*12500000000000^27 ≤ 4914916903591^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216767561 2500000000 4914916903591 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086544993/2000000000 : ℝ), (-2354423811/10000000000 : ℝ), (1216767561/2500000000 : ℝ)] ![(1813695778293/4000000000000 : ℝ), (15338270297599/100000000000000 : ℝ), (4914916903591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086544993/2000000000 : ℝ)|^35 ≤ (1813695778293/4000000000000 : ℝ)^27
        have hw : |(1086544993/2000000000 : ℝ)|=(1086544993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2354423811/10000000000 : ℝ)|^35 ≤ (15338270297599/100000000000000 : ℝ)^27
        have hw : |(-2354423811/10000000000 : ℝ)|=(2354423811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216767561/2500000000 : ℝ)|^35 ≤ (4914916903591/12500000000000 : ℝ)^27
        have hw : |(1216767561/2500000000 : ℝ)|=(1216767561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3031346967/10000000000 : ℝ)*x 0 + (624298579/1000000000 : ℝ)*x 1 + (-421312379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3031346967/10000000000 : ℝ)^35 ≤ (10641827508671/50000000000000 : ℝ)^27 := by
    have hnat : (3031346967 : ℕ)^35*50000000000000^27 ≤ 10641827508671^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031346967 10000000000 10641827508671 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624298579/1000000000 : ℝ)^35 ≤ (6787000316857/12500000000000 : ℝ)^27 := by
    have hnat : (624298579 : ℕ)^35*12500000000000^27 ≤ 6787000316857^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624298579 1000000000 6787000316857 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421312379/1250000000 : ℝ)^35 ≤ (12210171215443/50000000000000 : ℝ)^27 := by
    have hnat : (421312379 : ℕ)^35*50000000000000^27 ≤ 12210171215443^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421312379 1250000000 12210171215443 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3031346967/10000000000 : ℝ), (624298579/1000000000 : ℝ), (-421312379/1250000000 : ℝ)] ![(10641827508671/50000000000000 : ℝ), (6787000316857/12500000000000 : ℝ), (12210171215443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3031346967/10000000000 : ℝ)|^35 ≤ (10641827508671/50000000000000 : ℝ)^27
        have hw : |(3031346967/10000000000 : ℝ)|=(3031346967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624298579/1000000000 : ℝ)|^35 ≤ (6787000316857/12500000000000 : ℝ)^27
        have hw : |(624298579/1000000000 : ℝ)|=(624298579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421312379/1250000000 : ℝ)|^35 ≤ (12210171215443/50000000000000 : ℝ)^27
        have hw : |(-421312379/1250000000 : ℝ)|=(421312379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308021_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4673741331/10000000000 : ℝ)*x 0 + (996266399/2500000000 : ℝ)*x 1 + (2093555951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4673741331/10000000000 : ℝ)^35 ≤ (7461352091171/20000000000000 : ℝ)^27 := by
    have hnat : (4673741331 : ℕ)^35*20000000000000^27 ≤ 7461352091171^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673741331 10000000000 7461352091171 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996266399/2500000000 : ℝ)^35 ≤ (30342124458973/100000000000000 : ℝ)^27 := by
    have hnat : (996266399 : ℕ)^35*100000000000000^27 ≤ 30342124458973^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996266399 2500000000 30342124458973 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093555951/5000000000 : ℝ)^35 ≤ (8087778768081/25000000000000 : ℝ)^27 := by
    have hnat : (2093555951 : ℕ)^35*25000000000000^27 ≤ 8087778768081^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093555951 5000000000 8087778768081 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4673741331/10000000000 : ℝ), (996266399/2500000000 : ℝ), (2093555951/5000000000 : ℝ)] ![(7461352091171/20000000000000 : ℝ), (30342124458973/100000000000000 : ℝ), (8087778768081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4673741331/10000000000 : ℝ)|^35 ≤ (7461352091171/20000000000000 : ℝ)^27
        have hw : |(4673741331/10000000000 : ℝ)|=(4673741331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(996266399/2500000000 : ℝ)|^35 ≤ (30342124458973/100000000000000 : ℝ)^27
        have hw : |(996266399/2500000000 : ℝ)|=(996266399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2093555951/5000000000 : ℝ)|^35 ≤ (8087778768081/25000000000000 : ℝ)^27
        have hw : |(2093555951/5000000000 : ℝ)|=(2093555951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308021 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-499217739/1250000000 : ℝ)*X 0 0+(774747263/2000000000 : ℝ)*X 0 1+(992551821/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6134044551/10000000000 : ℝ)*X 1 0+(-1025191737/10000000000 : ℝ)*X 1 1+(2546834373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((47813099/250000000 : ℝ)*X 2 0+(782450233/1000000000 : ℝ)*X 2 1+(-475313423/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-4185464381/10000000000 : ℝ)*X 0 0+(2850384197/10000000000 : ℝ)*X 0 1+(5678034701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5506153001/10000000000 : ℝ)*X 1 0+(-257235259/10000000000 : ℝ)*X 1 1+(1531750243/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((589338343/10000000000 : ℝ)*X 2 0+(4754066019/5000000000 : ℝ)*X 2 1+(-99937643/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((798260899/2000000000 : ℝ)*X 0 0+(883482261/2000000000 : ℝ)*X 0 1+(2220672629/5000000000 : ℝ)*X 0 2+(798260899/2000000000 : ℝ)*X 1 0+(883482261/2000000000 : ℝ)*X 1 1+(2220672629/5000000000 : ℝ)*X 1 2+(798260899/2000000000 : ℝ)*X 2 0+(883482261/2000000000 : ℝ)*X 2 1+(2220672629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5178556997/10000000000 : ℝ)*X 0 0+(830511871/2500000000 : ℝ)*X 0 1+(536703587/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((367858341/625000000 : ℝ)*X 1 0+(-1078921131/10000000000 : ℝ)*X 1 1+(5319313147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((863470489/10000000000 : ℝ)*X 2 0+(8300622477/10000000000 : ℝ)*X 2 1+(-2580218827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((526906513/2000000000 : ℝ)*X 0 0+(92114527/200000000 : ℝ)*X 0 1+(5461239443/10000000000 : ℝ)*X 0 2+(526906513/2000000000 : ℝ)*X 1 0+(92114527/200000000 : ℝ)*X 1 1+(5461239443/10000000000 : ℝ)*X 1 2+(526906513/2000000000 : ℝ)*X 2 0+(92114527/200000000 : ℝ)*X 2 1+(5461239443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-596524341/2000000000 : ℝ)*X 0 0+(3931019803/10000000000 : ℝ)*X 0 1+(2899720187/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((7886017351/10000000000 : ℝ)*X 1 0+(-24151361/1000000000 : ℝ)*X 1 1+(3505635293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((118166447/2000000000 : ℝ)*X 2 0+(466466439/500000000 : ℝ)*X 2 1+(-229764057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((6885169603/10000000000 : ℝ)*X 0 0+(2526257897/10000000000 : ℝ)*X 0 1+(3060720321/10000000000 : ℝ)*X 0 2+(6885169603/10000000000 : ℝ)*X 1 0+(2526257897/10000000000 : ℝ)*X 1 1+(3060720321/10000000000 : ℝ)*X 1 2+(6885169603/10000000000 : ℝ)*X 2 0+(2526257897/10000000000 : ℝ)*X 2 1+(3060720321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21593/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21593/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (70812737489463523524087/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352307959147/1000000000000 : ℝ)*(base49) + (789027266019/1000000000000 : ℝ)*(base50) + (265358125739/500000000000 : ℝ)*(base59) + (2502321078277/1000000000000 : ℝ)*(major_s0_0) + (2502321078277/1000000000000 : ℝ)*(major_s0_1) + (2502321078277/1000000000000 : ℝ)*(major_s0_2) + (61109319/1000000000000 : ℝ)*(sp_s0_0) + (340777640997/100000000000 : ℝ)*(sp_s0_7) + (3407863068697/1000000000000 : ℝ)*(sp_s0_8) + (851914536699/250000000000 : ℝ)*(sp_s0_9) + (49898316191/31250000000 : ℝ)*(sp_s0_12) + (28248893/1000000000000 : ℝ)*(sp_s0_19) + (798419/31250000000 : ℝ)*(sp_s0_20) + (204921901/1000000000000 : ℝ)*(sp_s0_22) + (319354873401/200000000000 : ℝ)*(f.failure) + (3407863068697/1000000000000 : ℝ)*(f.sum) + (3917156847/10000000000000000000000 : ℝ)*base62 + (266946695087751/1250000000000000000000000000 : ℝ)*base64 + (584692099537249/1250000000000000000000000000 : ℝ)*base67 + (2129852781491971/10000000000000000000000000000 : ℝ)*base68 + (762524938193979/10000000000000000000000000000 : ℝ)*base70 + (142484540912249/1250000000000000000000000000 : ℝ)*base72 + (4419962648508029/10000000000000000000000000000 : ℝ)*base74 + (1382676837491971/10000000000000000000000000000 : ℝ)*base76 + (2859848457/5000000000000000000000 : ℝ)*base79 + (4111/20000000000000000 : ℝ)*base87 + (4111/20000000000000000 : ℝ)*base89 + (4111/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(571/4000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(571/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (66058032327162746553/9765625000000000000000000 : ℝ) := by norm_num
    linear_combination (226200486569/250000000000 : ℝ)*(base3) + (76530444191/1000000000000 : ℝ)*(base40) + (421720498871/1000000000000 : ℝ)*(base49) + (58323909233/125000000000 : ℝ)*(base59) + (354481044507/250000000000 : ℝ)*(major_s0_0) + (354481044507/250000000000 : ℝ)*(major_s0_1) + (354481044507/250000000000 : ℝ)*(major_s0_2) + (20763519/200000000000 : ℝ)*(sp_s0_1) + (2164807/62500000000 : ℝ)*(sp_s0_2) + (22374919/1000000000000 : ℝ)*(sp_s0_7) + (1314039/40000000000 : ℝ)*(sp_s0_8) + (482755445019/250000000000 : ℝ)*(sp_s0_13) + (2835709432701/1000000000000 : ℝ)*(sp_s0_14) + (482752379521/250000000000 : ℝ)*(sp_s0_15) + (226200486569/250000000000 : ℝ)*(f.failure) + (386208830999/200000000000 : ℝ)*(f.sum) + (1532748089/10000000000000000000000 : ℝ)*base62 + (223264298284009/312500000000000000000000000 : ℝ)*base65 + (47488008034009/312500000000000000000000000 : ℝ)*base67 + (313148810000739/2500000000000000000000000000 : ℝ)*base69 + (472456739772811/2500000000000000000000000000 : ℝ)*base71 + (113065781590991/312500000000000000000000000 : ℝ)*base73 + (113831171999261/2500000000000000000000000000 : ℝ)*base75 + (1459484577999261/2500000000000000000000000000 : ℝ)*base76 + (639529087/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (14559/25000000000000000 : ℝ)*base87 + (14559/25000000000000000 : ℝ)*base89 + (14559/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7083/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7083/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3935037431389718326881/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6691169/500000000000 : ℝ)*(base11) + (378656900293/500000000000 : ℝ)*(base40) + (28495609947/1000000000000 : ℝ)*(base49) + (901378136533/1000000000000 : ℝ)*(base50) + (552065214719/1000000000000 : ℝ)*(base59) + (185906868851/62500000000 : ℝ)*(major_s0_0) + (185906868851/62500000000 : ℝ)*(major_s0_1) + (185906868851/62500000000 : ℝ)*(major_s0_2) + (9512703/125000000000 : ℝ)*(sp_s0_0) + (593257/25000000000 : ℝ)*(sp_s0_15) + (253177493653/62500000000 : ℝ)*(sp_s0_20) + (405092938241/100000000000 : ℝ)*(sp_s0_21) + (405090565213/100000000000 : ℝ)*(sp_s0_22) + (23726077793/12500000000 : ℝ)*(sp_s0_25) + (23726077793/12500000000 : ℝ)*(f.failure) + (405092938241/100000000000 : ℝ)*(f.sum) + (130830769/312500000000000000000 : ℝ)*base63 + (38344561917987/78125000000000000000000000 : ℝ)*base65 + (27139848417987/78125000000000000000000000 : ℝ)*base67 + (188515793150627/625000000000000000000000000 : ℝ)*base69 + (120094484380477/625000000000000000000000000 : ℝ)*base70 + (6469949922361/9765625000000000000000000 : ℝ)*base73 + (195327830599373/625000000000000000000000000 : ℝ)*base75 + (168297982474373/625000000000000000000000000 : ℝ)*base76 + (1036891437/1000000000000000000000 : ℝ)*base79 + (1177/1250000000000000 : ℝ)*base86 + (1177/1250000000000000 : ℝ)*base88 + (1177/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (21593/50000 : ℝ) ^ (17/4 : ℝ) ≤ (2819730921000286863/100000000000000000000 : ℝ) := by
    have hpowers : (21593/50000 : ℝ)^17 ≤ (2819730921000286863/100000000000000000000 : ℝ)^4 := by
      have hnat : (21593 : ℕ)^17*100000000000000000000^4 ≤ 2819730921000286863^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21593 50000 2819730921000286863 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21593/50000 : ℝ)) (X := (2819730921000286863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102819730921000286863/100000000000000000000 : ℝ) ≤ (5032821471837787/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (102819730921000286863/100000000000000000000 : ℝ)^4 ≤ (5032821471837787/5000000000000000 : ℝ)^17 := by
      have hnat : (102819730921000286863 : ℕ)^4*5000000000000000^17 ≤ 5032821471837787^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102819730921000286863 100000000000000000000 5032821471837787 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032821471837787/5000000000000000 : ℝ)) (X := (102819730921000286863/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52819730921000286863/50000000000000000000 : ℝ) ≤ (2025984673859697/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (52819730921000286863/50000000000000000000 : ℝ)^4 ≤ (2025984673859697/2000000000000000 : ℝ)^17 := by
      have hnat : (52819730921000286863 : ℕ)^4*2000000000000000^17 ≤ 2025984673859697^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52819730921000286863 50000000000000000000 2025984673859697 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2025984673859697/2000000000000000 : ℝ)) (X := (52819730921000286863/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(32821471837787/2159300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(64280425622911/4318600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21593/50000 : ℝ)) (alpha := (32821471837787/2159300000000000 : ℝ)) (beta := (64280425622911/4318600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21593/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(32821471837787/2159300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(64280425622911/4318600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (571/4000 : ℝ) ^ (17/4 : ℝ) ≤ (12761992975395817/50000000000000000000 : ℝ) := by
    have hpowers : (571/4000 : ℝ)^17 ≤ (12761992975395817/50000000000000000000 : ℝ)^4 := by
      have hnat : (571 : ℕ)^17*50000000000000000000^4 ≤ 12761992975395817^4*4000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        571 4000 12761992975395817 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (571/4000 : ℝ)) (X := (12761992975395817/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50012761992975395817/50000000000000000000 : ℝ) ≤ (10000600505774007/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50012761992975395817/50000000000000000000 : ℝ)^4 ≤ (10000600505774007/10000000000000000 : ℝ)^17 := by
      have hnat : (50012761992975395817 : ℕ)^4*10000000000000000^17 ≤ 10000600505774007^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012761992975395817 50000000000000000000 10000600505774007 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000600505774007/10000000000000000 : ℝ)) (X := (50012761992975395817/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25012761992975395817/25000000000000000000 : ℝ) ≤ (500060044719029/500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (25012761992975395817/25000000000000000000 : ℝ)^4 ≤ (500060044719029/500000000000000 : ℝ)^17 := by
      have hnat : (25012761992975395817 : ℕ)^4*500000000000000^17 ≤ 500060044719029^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012761992975395817 25000000000000000000 500060044719029 500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500060044719029/500000000000000 : ℝ)) (X := (25012761992975395817/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(600505774007/1427500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1051468663/2500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (571/4000 : ℝ)) (alpha := (600505774007/1427500000000000 : ℝ)) (beta := (1051468663/2500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (571/4000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(600505774007/1427500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1051468663/2500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7083/12500 : ℝ) ^ (17/4 : ℝ) ≤ (894449287309398803/10000000000000000000 : ℝ) := by
    have hpowers : (7083/12500 : ℝ)^17 ≤ (894449287309398803/10000000000000000000 : ℝ)^4 := by
      have hnat : (7083 : ℕ)^17*10000000000000000000^4 ≤ 894449287309398803^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7083 12500 894449287309398803 10000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7083/12500 : ℝ)) (X := (894449287309398803/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10894449287309398803/10000000000000000000 : ℝ) ≤ (10203617827440461/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10894449287309398803/10000000000000000000 : ℝ)^4 ≤ (10203617827440461/10000000000000000 : ℝ)^17 := by
      have hnat : (10894449287309398803 : ℕ)^4*10000000000000000^17 ≤ 10203617827440461^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10894449287309398803 10000000000000000000 10203617827440461 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10203617827440461/10000000000000000 : ℝ)) (X := (10894449287309398803/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5894449287309398803/5000000000000000000 : ℝ) ≤ (2598706541035947/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5894449287309398803/5000000000000000000 : ℝ)^4 ≤ (2598706541035947/2500000000000000 : ℝ)^17 := by
      have hnat : (5894449287309398803 : ℕ)^4*2500000000000000^17 ≤ 2598706541035947^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5894449287309398803 5000000000000000000 2598706541035947 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2598706541035947/2500000000000000 : ℝ)) (X := (5894449287309398803/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(203617827440461/5666400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(191208336703327/5666400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (7083/12500 : ℝ)) (alpha := (203617827440461/5666400000000000 : ℝ)) (beta := (191208336703327/5666400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7083/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(203617827440461/5666400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(191208336703327/5666400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2034239641/5000000000 : ℝ)*X 0 0+(4258777263/10000000000 : ℝ)*X 0 1+(282729213/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1086544993/2000000000 : ℝ)*X 1 0+(-2354423811/10000000000 : ℝ)*X 1 1+(1216767561/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3031346967/10000000000 : ℝ)*X 2 0+(624298579/1000000000 : ℝ)*X 2 1+(-421312379/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4673741331/10000000000 : ℝ)*X 0 0+(996266399/2500000000 : ℝ)*X 0 1+(2093555951/5000000000 : ℝ)*X 0 2+(4673741331/10000000000 : ℝ)*X 1 0+(996266399/2500000000 : ℝ)*X 1 1+(2093555951/5000000000 : ℝ)*X 1 2+(4673741331/10000000000 : ℝ)*X 2 0+(996266399/2500000000 : ℝ)*X 2 1+(2093555951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308021_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-619446094916302949050366689877091/97033975610000000000000000000000 : ℝ) := by norm_num
    linear_combination (4457/100000000000 : ℝ)*(base3) + (5993/500000000000 : ℝ)*(base11) + (169169/1000000000000 : ℝ)*(base13) + (68021717339/500000000000 : ℝ)*(base40) + (639158037781/1000000000000 : ℝ)*(base49) + (454025600409/1000000000000 : ℝ)*(base50) + (209482304667/1000000000000 : ℝ)*(base59) + (369/50000000000 : ℝ)*(ratio_s0_2) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (156711/100000 : ℝ)*(major_s1_2) + (4156123473/1953125000 : ℝ)*(sp_s1_0) + (2127935443901/1000000000000 : ℝ)*(sp_s1_1) + (2127935399331/1000000000000 : ℝ)*(sp_s1_2) + (99999995543/100000000000 : ℝ)*(sp_s1_6) + (2127935399331/1000000000000 : ℝ)*(f.sum) + (2591731992828719/6740655000000000000000000000 : ℝ)*base62 + (125844888391/184453125000000000000000 : ℝ)*base64 + (893336083/2500000000000000000000 : ℝ)*base67 + (12334656601/4722000000000000000000000 : ℝ)*base69 + (450881984153512537/509810730000000000000000000000 : ℝ)*base70 + (9069945407691/26991250000000000000000000 : ℝ)*base73 + (3258195788397/5710000000000000000000000 : ℝ)*base74 + (11484588258261/21593000000000000000000000 : ℝ)*base76 + (35574129953269/53982500000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p008_b012 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 21 ≤ c.val) (hhi : c.val < 22)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=21 := by omega
  rcases hc with rfl
  · exact collision_c308021 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 21 ≤ c.val) (hhi : c.val < 22)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b012 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
