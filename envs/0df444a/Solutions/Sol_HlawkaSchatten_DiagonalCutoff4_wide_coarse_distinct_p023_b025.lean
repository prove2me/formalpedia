-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:10.705855+00:00
-- url     : https://prove2.me/submissions/eadd3cf1-8498-4433-8b8a-b1d7e199f0a3

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
theorem collision_support_c323047_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-54857569/2000000000 : ℝ)*x 0 + (-1221486553/2000000000 : ℝ)*x 1 + (258341969/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54857569/2000000000 : ℝ)^85 ≤ (238276689729/20000000000000 : ℝ)^69 := by
    have hnat : (54857569 : ℕ)^85*20000000000000^69 ≤ 238276689729^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54857569 2000000000 238276689729 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221486553/2000000000 : ℝ)^85 ≤ (13618922499/25000000000 : ℝ)^69 := by
    have hnat : (1221486553 : ℕ)^85*25000000000^69 ≤ 13618922499^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221486553 2000000000 13618922499 25000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258341969/500000000 : ℝ)^85 ≤ (44332926536227/100000000000000 : ℝ)^69 := by
    have hnat : (258341969 : ℕ)^85*100000000000000^69 ≤ 44332926536227^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258341969 500000000 44332926536227 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54857569/2000000000 : ℝ), (-1221486553/2000000000 : ℝ), (258341969/500000000 : ℝ)] ![(238276689729/20000000000000 : ℝ), (13618922499/25000000000 : ℝ), (44332926536227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54857569/2000000000 : ℝ)|^85 ≤ (238276689729/20000000000000 : ℝ)^69
        have hw : |(-54857569/2000000000 : ℝ)|=(54857569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1221486553/2000000000 : ℝ)|^85 ≤ (13618922499/25000000000 : ℝ)^69
        have hw : |(-1221486553/2000000000 : ℝ)|=(1221486553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258341969/500000000 : ℝ)|^85 ≤ (44332926536227/100000000000000 : ℝ)^69
        have hw : |(258341969/500000000 : ℝ)|=(258341969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5125445641/10000000000 : ℝ)*x 0 + (1849493961/5000000000 : ℝ)*x 1 + (3426822729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5125445641/10000000000 : ℝ)^85 ≤ (43895805693993/100000000000000 : ℝ)^69 := by
    have hnat : (5125445641 : ℕ)^85*100000000000000^69 ≤ 43895805693993^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125445641 10000000000 43895805693993 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1849493961/5000000000 : ℝ)^85 ≤ (1468582101201/5000000000000 : ℝ)^69 := by
    have hnat : (1849493961 : ℕ)^85*5000000000000^69 ≤ 1468582101201^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849493961 5000000000 1468582101201 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3426822729/10000000000 : ℝ)^85 ≤ (1336627613207/5000000000000 : ℝ)^69 := by
    have hnat : (3426822729 : ℕ)^85*5000000000000^69 ≤ 1336627613207^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3426822729 10000000000 1336627613207 5000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5125445641/10000000000 : ℝ), (1849493961/5000000000 : ℝ), (3426822729/10000000000 : ℝ)] ![(43895805693993/100000000000000 : ℝ), (1468582101201/5000000000000 : ℝ), (1336627613207/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5125445641/10000000000 : ℝ)|^85 ≤ (43895805693993/100000000000000 : ℝ)^69
        have hw : |(5125445641/10000000000 : ℝ)|=(5125445641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1849493961/5000000000 : ℝ)|^85 ≤ (1468582101201/5000000000000 : ℝ)^69
        have hw : |(1849493961/5000000000 : ℝ)|=(1849493961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3426822729/10000000000 : ℝ)|^85 ≤ (1336627613207/5000000000000 : ℝ)^69
        have hw : |(3426822729/10000000000 : ℝ)|=(3426822729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1099248387/2000000000 : ℝ)*x 0 + (-365971639/1000000000 : ℝ)*x 1 + (-3051406511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099248387/2000000000 : ℝ)^85 ≤ (47840009128369/100000000000000 : ℝ)^69 := by
    have hnat : (1099248387 : ℕ)^85*100000000000000^69 ≤ 47840009128369^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099248387 2000000000 47840009128369 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365971639/1000000000 : ℝ)^85 ≤ (7246993277783/25000000000000 : ℝ)^69 := by
    have hnat : (365971639 : ℕ)^85*25000000000000^69 ≤ 7246993277783^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365971639 1000000000 7246993277783 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3051406511/10000000000 : ℝ)^85 ≤ (23172017755269/100000000000000 : ℝ)^69 := by
    have hnat : (3051406511 : ℕ)^85*100000000000000^69 ≤ 23172017755269^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051406511 10000000000 23172017755269 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099248387/2000000000 : ℝ), (-365971639/1000000000 : ℝ), (-3051406511/10000000000 : ℝ)] ![(47840009128369/100000000000000 : ℝ), (7246993277783/25000000000000 : ℝ), (23172017755269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099248387/2000000000 : ℝ)|^85 ≤ (47840009128369/100000000000000 : ℝ)^69
        have hw : |(1099248387/2000000000 : ℝ)|=(1099248387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-365971639/1000000000 : ℝ)|^85 ≤ (7246993277783/25000000000000 : ℝ)^69
        have hw : |(-365971639/1000000000 : ℝ)|=(365971639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3051406511/10000000000 : ℝ)|^85 ≤ (23172017755269/100000000000000 : ℝ)^69
        have hw : |(-3051406511/10000000000 : ℝ)|=(3051406511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-210858799/10000000000 : ℝ)*x 0 + (-1533207833/2000000000 : ℝ)*x 1 + (1730426121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210858799/10000000000 : ℝ)^85 ≤ (430846067887/50000000000000 : ℝ)^69 := by
    have hnat : (210858799 : ℕ)^85*50000000000000^69 ≤ 430846067887^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210858799 10000000000 430846067887 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1533207833/2000000000 : ℝ)^85 ≤ (72078359999909/100000000000000 : ℝ)^69 := by
    have hnat : (1533207833 : ℕ)^85*100000000000000^69 ≤ 72078359999909^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533207833 2000000000 72078359999909 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1730426121/5000000000 : ℝ)^85 ≤ (5411989570791/20000000000000 : ℝ)^69 := by
    have hnat : (1730426121 : ℕ)^85*20000000000000^69 ≤ 5411989570791^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730426121 5000000000 5411989570791 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210858799/10000000000 : ℝ), (-1533207833/2000000000 : ℝ), (1730426121/5000000000 : ℝ)] ![(430846067887/50000000000000 : ℝ), (72078359999909/100000000000000 : ℝ), (5411989570791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210858799/10000000000 : ℝ)|^85 ≤ (430846067887/50000000000000 : ℝ)^69
        have hw : |(-210858799/10000000000 : ℝ)|=(210858799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1533207833/2000000000 : ℝ)|^85 ≤ (72078359999909/100000000000000 : ℝ)^69
        have hw : |(-1533207833/2000000000 : ℝ)|=(1533207833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1730426121/5000000000 : ℝ)|^85 ≤ (5411989570791/20000000000000 : ℝ)^69
        have hw : |(1730426121/5000000000 : ℝ)|=(1730426121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3140234733/10000000000 : ℝ)*x 0 + (5130420663/10000000000 : ℝ)*x 1 + (1985061093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3140234733/10000000000 : ℝ)^85 ≤ (24005770303183/100000000000000 : ℝ)^69 := by
    have hnat : (3140234733 : ℕ)^85*100000000000000^69 ≤ 24005770303183^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140234733 10000000000 24005770303183 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130420663/10000000000 : ℝ)^85 ≤ (4394829914123/10000000000000 : ℝ)^69 := by
    have hnat : (5130420663 : ℕ)^85*10000000000000^69 ≤ 4394829914123^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130420663 10000000000 4394829914123 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985061093/5000000000 : ℝ)^85 ≤ (6409186107887/20000000000000 : ℝ)^69 := by
    have hnat : (1985061093 : ℕ)^85*20000000000000^69 ≤ 6409186107887^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985061093 5000000000 6409186107887 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3140234733/10000000000 : ℝ), (5130420663/10000000000 : ℝ), (1985061093/5000000000 : ℝ)] ![(24005770303183/100000000000000 : ℝ), (4394829914123/10000000000000 : ℝ), (6409186107887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3140234733/10000000000 : ℝ)|^85 ≤ (24005770303183/100000000000000 : ℝ)^69
        have hw : |(3140234733/10000000000 : ℝ)|=(3140234733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130420663/10000000000 : ℝ)|^85 ≤ (4394829914123/10000000000000 : ℝ)^69
        have hw : |(5130420663/10000000000 : ℝ)|=(5130420663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1985061093/5000000000 : ℝ)|^85 ≤ (6409186107887/20000000000000 : ℝ)^69
        have hw : |(1985061093/5000000000 : ℝ)|=(1985061093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (595874911/1250000000 : ℝ)*x 0 + (-329639809/1000000000 : ℝ)*x 1 + (-4202286627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (595874911/1250000000 : ℝ)^85 ≤ (2509084395741/6250000000000 : ℝ)^69 := by
    have hnat : (595874911 : ℕ)^85*6250000000000^69 ≤ 2509084395741^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595874911 1250000000 2509084395741 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329639809/1000000000 : ℝ)^85 ≤ (5096954170673/20000000000000 : ℝ)^69 := by
    have hnat : (329639809 : ℕ)^85*20000000000000^69 ≤ 5096954170673^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329639809 1000000000 5096954170673 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4202286627/10000000000 : ℝ)^85 ≤ (6873975760823/20000000000000 : ℝ)^69 := by
    have hnat : (4202286627 : ℕ)^85*20000000000000^69 ≤ 6873975760823^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202286627 10000000000 6873975760823 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(595874911/1250000000 : ℝ), (-329639809/1000000000 : ℝ), (-4202286627/10000000000 : ℝ)] ![(2509084395741/6250000000000 : ℝ), (5096954170673/20000000000000 : ℝ), (6873975760823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(595874911/1250000000 : ℝ)|^85 ≤ (2509084395741/6250000000000 : ℝ)^69
        have hw : |(595874911/1250000000 : ℝ)|=(595874911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329639809/1000000000 : ℝ)|^85 ≤ (5096954170673/20000000000000 : ℝ)^69
        have hw : |(-329639809/1000000000 : ℝ)|=(329639809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4202286627/10000000000 : ℝ)|^85 ≤ (6873975760823/20000000000000 : ℝ)^69
        have hw : |(-4202286627/10000000000 : ℝ)|=(4202286627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2546754327/5000000000 : ℝ)*x 0 + (3929761/10000000000 : ℝ)*x 1 + (1257021861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2546754327/5000000000 : ℝ)^85 ≤ (43559107489091/100000000000000 : ℝ)^69 := by
    have hnat : (2546754327 : ℕ)^85*100000000000000^69 ≤ 43559107489091^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546754327 5000000000 43559107489091 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3929761/10000000000 : ℝ)^85 ≤ (3188775487/50000000000000 : ℝ)^69 := by
    have hnat : (3929761 : ℕ)^85*50000000000000^69 ≤ 3188775487^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929761 10000000000 3188775487 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257021861/2000000000 : ℝ)^85 ≤ (3527157184413/6250000000000 : ℝ)^69 := by
    have hnat : (1257021861 : ℕ)^85*6250000000000^69 ≤ 3527157184413^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257021861 2000000000 3527157184413 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2546754327/5000000000 : ℝ), (3929761/10000000000 : ℝ), (1257021861/2000000000 : ℝ)] ![(43559107489091/100000000000000 : ℝ), (3188775487/50000000000000 : ℝ), (3527157184413/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2546754327/5000000000 : ℝ)|^85 ≤ (43559107489091/100000000000000 : ℝ)^69
        have hw : |(2546754327/5000000000 : ℝ)|=(2546754327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3929761/10000000000 : ℝ)|^85 ≤ (3188775487/50000000000000 : ℝ)^69
        have hw : |(3929761/10000000000 : ℝ)|=(3929761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1257021861/2000000000 : ℝ)|^85 ≤ (3527157184413/6250000000000 : ℝ)^69
        have hw : |(1257021861/2000000000 : ℝ)|=(1257021861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1/1250000000 : ℝ)*x 0 + (-1178213281/2500000000 : ℝ)*x 1 + (6642702133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1/1250000000 : ℝ)^85 ≤ (311/50000000000000 : ℝ)^69 := by
    have hnat : (1 : ℕ)^85*50000000000000^69 ≤ 311^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1250000000 311 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178213281/2500000000 : ℝ)^85 ≤ (39584362156661/100000000000000 : ℝ)^69 := by
    have hnat : (1178213281 : ℕ)^85*100000000000000^69 ≤ 39584362156661^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178213281 2500000000 39584362156661 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6642702133/10000000000 : ℝ)^85 ≤ (30207818919221/50000000000000 : ℝ)^69 := by
    have hnat : (6642702133 : ℕ)^85*50000000000000^69 ≤ 30207818919221^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6642702133 10000000000 30207818919221 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1/1250000000 : ℝ), (-1178213281/2500000000 : ℝ), (6642702133/10000000000 : ℝ)] ![(311/50000000000000 : ℝ), (39584362156661/100000000000000 : ℝ), (30207818919221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1/1250000000 : ℝ)|^85 ≤ (311/50000000000000 : ℝ)^69
        have hw : |(-1/1250000000 : ℝ)|=(1/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1178213281/2500000000 : ℝ)|^85 ≤ (39584362156661/100000000000000 : ℝ)^69
        have hw : |(-1178213281/2500000000 : ℝ)|=(1178213281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6642702133/10000000000 : ℝ)|^85 ≤ (30207818919221/50000000000000 : ℝ)^69
        have hw : |(6642702133/10000000000 : ℝ)|=(6642702133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9903841/31250000 : ℝ)*x 0 + (4588118259/10000000000 : ℝ)*x 1 + (1125720263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9903841/31250000 : ℝ)^85 ≤ (379361075733/1562500000000 : ℝ)^69 := by
    have hnat : (9903841 : ℕ)^85*1562500000000^69 ≤ 379361075733^69*31250000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9903841 31250000 379361075733 1562500000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4588118259/10000000000 : ℝ)^85 ≤ (38297732561369/100000000000000 : ℝ)^69 := by
    have hnat : (4588118259 : ℕ)^85*100000000000000^69 ≤ 38297732561369^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4588118259 10000000000 38297732561369 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125720263/2500000000 : ℝ)^85 ≤ (292368426439/781250000000 : ℝ)^69 := by
    have hnat : (1125720263 : ℕ)^85*781250000000^69 ≤ 292368426439^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125720263 2500000000 292368426439 781250000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9903841/31250000 : ℝ), (4588118259/10000000000 : ℝ), (1125720263/2500000000 : ℝ)] ![(379361075733/1562500000000 : ℝ), (38297732561369/100000000000000 : ℝ), (292368426439/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9903841/31250000 : ℝ)|^85 ≤ (379361075733/1562500000000 : ℝ)^69
        have hw : |(9903841/31250000 : ℝ)|=(9903841/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4588118259/10000000000 : ℝ)|^85 ≤ (38297732561369/100000000000000 : ℝ)^69
        have hw : |(4588118259/10000000000 : ℝ)|=(4588118259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125720263/2500000000 : ℝ)|^85 ≤ (292368426439/781250000000 : ℝ)^69
        have hw : |(1125720263/2500000000 : ℝ)|=(1125720263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3357710087/5000000000 : ℝ)*x 0 + (-534991487/2000000000 : ℝ)*x 1 + (-1302303977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3357710087/5000000000 : ℝ)^85 ≤ (61231404445609/100000000000000 : ℝ)^69 := by
    have hnat : (3357710087 : ℕ)^85*100000000000000^69 ≤ 61231404445609^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357710087 5000000000 61231404445609 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534991487/2000000000 : ℝ)^85 ≤ (3940495034907/20000000000000 : ℝ)^69 := by
    have hnat : (534991487 : ℕ)^85*20000000000000^69 ≤ 3940495034907^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534991487 2000000000 3940495034907 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302303977/5000000000 : ℝ)^85 ≤ (19066120373047/100000000000000 : ℝ)^69 := by
    have hnat : (1302303977 : ℕ)^85*100000000000000^69 ≤ 19066120373047^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302303977 5000000000 19066120373047 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3357710087/5000000000 : ℝ), (-534991487/2000000000 : ℝ), (-1302303977/5000000000 : ℝ)] ![(61231404445609/100000000000000 : ℝ), (3940495034907/20000000000000 : ℝ), (19066120373047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3357710087/5000000000 : ℝ)|^85 ≤ (61231404445609/100000000000000 : ℝ)^69
        have hw : |(3357710087/5000000000 : ℝ)|=(3357710087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534991487/2000000000 : ℝ)|^85 ≤ (3940495034907/20000000000000 : ℝ)^69
        have hw : |(-534991487/2000000000 : ℝ)|=(534991487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1302303977/5000000000 : ℝ)|^85 ≤ (19066120373047/100000000000000 : ℝ)^69
        have hw : |(-1302303977/5000000000 : ℝ)|=(1302303977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4133192781/5000000000 : ℝ)*x 0 + (-75765729/5000000000 : ℝ)*x 1 + (2744199891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133192781/5000000000 : ℝ)^85 ≤ (7909380649717/10000000000000 : ℝ)^69 := by
    have hnat : (4133192781 : ℕ)^85*10000000000000^69 ≤ 7909380649717^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133192781 5000000000 7909380649717 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75765729/5000000000 : ℝ)^85 ≤ (22943010269/4000000000000 : ℝ)^69 := by
    have hnat : (75765729 : ℕ)^85*4000000000000^69 ≤ 22943010269^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75765729 5000000000 22943010269 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744199891/10000000000 : ℝ)^85 ≤ (20332618228627/100000000000000 : ℝ)^69 := by
    have hnat : (2744199891 : ℕ)^85*100000000000000^69 ≤ 20332618228627^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744199891 10000000000 20332618228627 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133192781/5000000000 : ℝ), (-75765729/5000000000 : ℝ), (2744199891/10000000000 : ℝ)] ![(7909380649717/10000000000000 : ℝ), (22943010269/4000000000000 : ℝ), (20332618228627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133192781/5000000000 : ℝ)|^85 ≤ (7909380649717/10000000000000 : ℝ)^69
        have hw : |(4133192781/5000000000 : ℝ)|=(4133192781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75765729/5000000000 : ℝ)|^85 ≤ (22943010269/4000000000000 : ℝ)^69
        have hw : |(-75765729/5000000000 : ℝ)|=(75765729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744199891/10000000000 : ℝ)|^85 ≤ (20332618228627/100000000000000 : ℝ)^69
        have hw : |(2744199891/10000000000 : ℝ)|=(2744199891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-93162523/2000000000 : ℝ)*x 0 + (-101323261/125000000 : ℝ)*x 1 + (345402093/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93162523/2000000000 : ℝ)^85 ≤ (285956964391/12500000000000 : ℝ)^69 := by
    have hnat : (93162523 : ℕ)^85*12500000000000^69 ≤ 285956964391^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93162523 2000000000 285956964391 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101323261/125000000 : ℝ)^85 ≤ (77206012276899/100000000000000 : ℝ)^69 := by
    have hnat : (101323261 : ℕ)^85*100000000000000^69 ≤ 77206012276899^69*125000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101323261 125000000 77206012276899 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345402093/1250000000 : ℝ)^85 ≤ (640822874749/3125000000000 : ℝ)^69 := by
    have hnat : (345402093 : ℕ)^85*3125000000000^69 ≤ 640822874749^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345402093 1250000000 640822874749 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93162523/2000000000 : ℝ), (-101323261/125000000 : ℝ), (345402093/1250000000 : ℝ)] ![(285956964391/12500000000000 : ℝ), (77206012276899/100000000000000 : ℝ), (640822874749/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93162523/2000000000 : ℝ)|^85 ≤ (285956964391/12500000000000 : ℝ)^69
        have hw : |(-93162523/2000000000 : ℝ)|=(93162523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101323261/125000000 : ℝ)|^85 ≤ (77206012276899/100000000000000 : ℝ)^69
        have hw : |(-101323261/125000000 : ℝ)|=(101323261/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345402093/1250000000 : ℝ)|^85 ≤ (640822874749/3125000000000 : ℝ)^69
        have hw : |(345402093/1250000000 : ℝ)|=(345402093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6583734401/10000000000 : ℝ)*x 0 + (783646207/2500000000 : ℝ)*x 1 + (573117839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6583734401/10000000000 : ℝ)^85 ≤ (29877821447991/50000000000000 : ℝ)^69 := by
    have hnat : (6583734401 : ℕ)^85*50000000000000^69 ≤ 29877821447991^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6583734401 10000000000 29877821447991 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (783646207/2500000000 : ℝ)^85 ≤ (23952574929061/100000000000000 : ℝ)^69 := by
    have hnat : (783646207 : ℕ)^85*100000000000000^69 ≤ 23952574929061^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783646207 2500000000 23952574929061 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573117839/2500000000 : ℝ)^85 ≤ (8145891082643/50000000000000 : ℝ)^69 := by
    have hnat : (573117839 : ℕ)^85*50000000000000^69 ≤ 8145891082643^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573117839 2500000000 8145891082643 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6583734401/10000000000 : ℝ), (783646207/2500000000 : ℝ), (573117839/2500000000 : ℝ)] ![(29877821447991/50000000000000 : ℝ), (23952574929061/100000000000000 : ℝ), (8145891082643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6583734401/10000000000 : ℝ)|^85 ≤ (29877821447991/50000000000000 : ℝ)^69
        have hw : |(6583734401/10000000000 : ℝ)|=(6583734401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(783646207/2500000000 : ℝ)|^85 ≤ (23952574929061/100000000000000 : ℝ)^69
        have hw : |(783646207/2500000000 : ℝ)|=(783646207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(573117839/2500000000 : ℝ)|^85 ≤ (8145891082643/50000000000000 : ℝ)^69
        have hw : |(573117839/2500000000 : ℝ)|=(573117839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2295711773/10000000000 : ℝ)*x 0 + (-3309056869/5000000000 : ℝ)*x 1 + (-3090639359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295711773/10000000000 : ℝ)^85 ≤ (2040019406261/12500000000000 : ℝ)^69 := by
    have hnat : (2295711773 : ℕ)^85*12500000000000^69 ≤ 2040019406261^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295711773 10000000000 2040019406261 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3309056869/5000000000 : ℝ)^85 ≤ (7517533370739/12500000000000 : ℝ)^69 := by
    have hnat : (3309056869 : ℕ)^85*12500000000000^69 ≤ 7517533370739^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3309056869 5000000000 7517533370739 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3090639359/10000000000 : ℝ)^85 ≤ (1471223610609/6250000000000 : ℝ)^69 := by
    have hnat : (3090639359 : ℕ)^85*6250000000000^69 ≤ 1471223610609^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3090639359 10000000000 1471223610609 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2295711773/10000000000 : ℝ), (-3309056869/5000000000 : ℝ), (-3090639359/10000000000 : ℝ)] ![(2040019406261/12500000000000 : ℝ), (7517533370739/12500000000000 : ℝ), (1471223610609/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2295711773/10000000000 : ℝ)|^85 ≤ (2040019406261/12500000000000 : ℝ)^69
        have hw : |(2295711773/10000000000 : ℝ)|=(2295711773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3309056869/5000000000 : ℝ)|^85 ≤ (7517533370739/12500000000000 : ℝ)^69
        have hw : |(-3309056869/5000000000 : ℝ)|=(3309056869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3090639359/10000000000 : ℝ)|^85 ≤ (1471223610609/6250000000000 : ℝ)^69
        have hw : |(-3090639359/10000000000 : ℝ)|=(3090639359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s0_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8121032821/10000000000 : ℝ)*x 0 + (499/10000000000 : ℝ)*x 1 + (373978359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8121032821/10000000000 : ℝ)^85 ≤ (4836504281009/6250000000000 : ℝ)^69 := by
    have hnat : (8121032821 : ℕ)^85*6250000000000^69 ≤ 4836504281009^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8121032821 10000000000 4836504281009 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499/10000000000 : ℝ)^85 ≤ (101137/100000000000000 : ℝ)^69 := by
    have hnat : (499 : ℕ)^85*100000000000000^69 ≤ 101137^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499 10000000000 101137 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373978359/1250000000 : ℝ)^85 ≤ (22615931391627/100000000000000 : ℝ)^69 := by
    have hnat : (373978359 : ℕ)^85*100000000000000^69 ≤ 22615931391627^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373978359 1250000000 22615931391627 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8121032821/10000000000 : ℝ), (499/10000000000 : ℝ), (373978359/1250000000 : ℝ)] ![(4836504281009/6250000000000 : ℝ), (101137/100000000000000 : ℝ), (22615931391627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8121032821/10000000000 : ℝ)|^85 ≤ (4836504281009/6250000000000 : ℝ)^69
        have hw : |(8121032821/10000000000 : ℝ)|=(8121032821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499/10000000000 : ℝ)|^85 ≤ (101137/100000000000000 : ℝ)^69
        have hw : |(499/10000000000 : ℝ)|=(499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373978359/1250000000 : ℝ)|^85 ≤ (22615931391627/100000000000000 : ℝ)^69
        have hw : |(373978359/1250000000 : ℝ)|=(373978359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1725472341/10000000000 : ℝ)*x 0 + (-50037011/100000000 : ℝ)*x 1 + (41523783/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725472341/10000000000 : ℝ)^85 ≤ (11480455854261/100000000000000 : ℝ)^69 := by
    have hnat : (1725472341 : ℕ)^85*100000000000000^69 ≤ 11480455854261^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725472341 10000000000 11480455854261 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50037011/100000000 : ℝ)^85 ≤ (42614933876397/100000000000000 : ℝ)^69 := by
    have hnat : (50037011 : ℕ)^85*100000000000000^69 ≤ 42614933876397^69*100000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50037011 100000000 42614933876397 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41523783/78125000 : ℝ)^85 ≤ (11476152563941/25000000000000 : ℝ)^69 := by
    have hnat : (41523783 : ℕ)^85*25000000000000^69 ≤ 11476152563941^69*78125000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41523783 78125000 11476152563941 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1725472341/10000000000 : ℝ), (-50037011/100000000 : ℝ), (41523783/78125000 : ℝ)] ![(11480455854261/100000000000000 : ℝ), (42614933876397/100000000000000 : ℝ), (11476152563941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1725472341/10000000000 : ℝ)|^85 ≤ (11480455854261/100000000000000 : ℝ)^69
        have hw : |(-1725472341/10000000000 : ℝ)|=(1725472341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50037011/100000000 : ℝ)|^85 ≤ (42614933876397/100000000000000 : ℝ)^69
        have hw : |(-50037011/100000000 : ℝ)|=(50037011/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41523783/78125000 : ℝ)|^85 ≤ (11476152563941/25000000000000 : ℝ)^69
        have hw : |(41523783/78125000 : ℝ)|=(41523783/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4940045709/10000000000 : ℝ)*x 0 + (1974374921/5000000000 : ℝ)*x 1 + (26985761/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4940045709/10000000000 : ℝ)^85 ≤ (41948077455439/100000000000000 : ℝ)^69 := by
    have hnat : (4940045709 : ℕ)^85*100000000000000^69 ≤ 41948077455439^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940045709 10000000000 41948077455439 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974374921/5000000000 : ℝ)^85 ≤ (1989596729489/6250000000000 : ℝ)^69 := by
    have hnat : (1974374921 : ℕ)^85*6250000000000^69 ≤ 1989596729489^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974374921 5000000000 1989596729489 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26985761/80000000 : ℝ)^85 ≤ (26218374860817/100000000000000 : ℝ)^69 := by
    have hnat : (26985761 : ℕ)^85*100000000000000^69 ≤ 26218374860817^69*80000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26985761 80000000 26218374860817 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4940045709/10000000000 : ℝ), (1974374921/5000000000 : ℝ), (26985761/80000000 : ℝ)] ![(41948077455439/100000000000000 : ℝ), (1989596729489/6250000000000 : ℝ), (26218374860817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4940045709/10000000000 : ℝ)|^85 ≤ (41948077455439/100000000000000 : ℝ)^69
        have hw : |(4940045709/10000000000 : ℝ)|=(4940045709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1974374921/5000000000 : ℝ)|^85 ≤ (1989596729489/6250000000000 : ℝ)^69
        have hw : |(1974374921/5000000000 : ℝ)|=(1974374921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26985761/80000000 : ℝ)|^85 ≤ (26218374860817/100000000000000 : ℝ)^69
        have hw : |(26985761/80000000 : ℝ)|=(26985761/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (38624303/80000000 : ℝ)*x 0 + (-4046597059/10000000000 : ℝ)*x 1 + (-848368333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38624303/80000000 : ℝ)^85 ≤ (20389760853107/50000000000000 : ℝ)^69 := by
    have hnat : (38624303 : ℕ)^85*50000000000000^69 ≤ 20389760853107^69*80000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38624303 80000000 20389760853107 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4046597059/10000000000 : ℝ)^85 ≤ (32808047678507/100000000000000 : ℝ)^69 := by
    have hnat : (4046597059 : ℕ)^85*100000000000000^69 ≤ 32808047678507^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046597059 10000000000 32808047678507 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848368333/2500000000 : ℝ)^85 ≤ (825388456077/3125000000000 : ℝ)^69 := by
    have hnat : (848368333 : ℕ)^85*3125000000000^69 ≤ 825388456077^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848368333 2500000000 825388456077 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(38624303/80000000 : ℝ), (-4046597059/10000000000 : ℝ), (-848368333/2500000000 : ℝ)] ![(20389760853107/50000000000000 : ℝ), (32808047678507/100000000000000 : ℝ), (825388456077/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(38624303/80000000 : ℝ)|^85 ≤ (20389760853107/50000000000000 : ℝ)^69
        have hw : |(38624303/80000000 : ℝ)|=(38624303/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4046597059/10000000000 : ℝ)|^85 ≤ (32808047678507/100000000000000 : ℝ)^69
        have hw : |(-4046597059/10000000000 : ℝ)|=(4046597059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-848368333/2500000000 : ℝ)|^85 ≤ (825388456077/3125000000000 : ℝ)^69
        have hw : |(-848368333/2500000000 : ℝ)|=(848368333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323047_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1502793267/2500000000 : ℝ)*x 0 + (-83674991/500000000 : ℝ)*x 1 + (4316486629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1502793267/2500000000 : ℝ)^85 ≤ (13354985177543/25000000000000 : ℝ)^69 := by
    have hnat : (1502793267 : ℕ)^85*25000000000000^69 ≤ 13354985177543^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502793267 2500000000 13354985177543 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83674991/500000000 : ℝ)^85 ≤ (11055969700723/100000000000000 : ℝ)^69 := by
    have hnat : (83674991 : ℕ)^85*100000000000000^69 ≤ 11055969700723^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83674991 500000000 11055969700723 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316486629/10000000000 : ℝ)^85 ≤ (4440511196751/12500000000000 : ℝ)^69 := by
    have hnat : (4316486629 : ℕ)^85*12500000000000^69 ≤ 4440511196751^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316486629 10000000000 4440511196751 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1502793267/2500000000 : ℝ), (-83674991/500000000 : ℝ), (4316486629/10000000000 : ℝ)] ![(13354985177543/25000000000000 : ℝ), (11055969700723/100000000000000 : ℝ), (4440511196751/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1502793267/2500000000 : ℝ)|^85 ≤ (13354985177543/25000000000000 : ℝ)^69
        have hw : |(1502793267/2500000000 : ℝ)|=(1502793267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83674991/500000000 : ℝ)|^85 ≤ (11055969700723/100000000000000 : ℝ)^69
        have hw : |(-83674991/500000000 : ℝ)|=(83674991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316486629/10000000000 : ℝ)|^85 ≤ (4440511196751/12500000000000 : ℝ)^69
        have hw : |(4316486629/10000000000 : ℝ)|=(4316486629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323047 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (83/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^83 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^83*1^16 ≤ 1^16*1^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2285913930952523/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2285913930952523/2000000000000000 : ℝ)^83 := by
      have hnat : (2 : ℕ)^16*2000000000000000^83 ≤ 2285913930952523^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2285913930952523 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2285913930952523/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (1544846006891271/1250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (1544846006891271/1250000000000000 : ℝ)^83 := by
      have hnat : (3 : ℕ)^16*1250000000000000^83 ≤ 1544846006891271^83*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 1544846006891271 1250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1544846006891271/1250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-54857569/2000000000 : ℝ)*X 0 0+(-1221486553/2000000000 : ℝ)*X 0 1+(258341969/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5125445641/10000000000 : ℝ)*X 1 0+(1849493961/5000000000 : ℝ)*X 1 1+(3426822729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1099248387/2000000000 : ℝ)*X 2 0+(-365971639/1000000000 : ℝ)*X 2 1+(-3051406511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-210858799/10000000000 : ℝ)*X 0 0+(-1533207833/2000000000 : ℝ)*X 0 1+(1730426121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3140234733/10000000000 : ℝ)*X 1 0+(5130420663/10000000000 : ℝ)*X 1 1+(1985061093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((595874911/1250000000 : ℝ)*X 2 0+(-329639809/1000000000 : ℝ)*X 2 1+(-4202286627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2546754327/5000000000 : ℝ)*X 0 0+(3929761/10000000000 : ℝ)*X 0 1+(1257021861/2000000000 : ℝ)*X 0 2+(2546754327/5000000000 : ℝ)*X 1 0+(3929761/10000000000 : ℝ)*X 1 1+(1257021861/2000000000 : ℝ)*X 1 2+(2546754327/5000000000 : ℝ)*X 2 0+(3929761/10000000000 : ℝ)*X 2 1+(1257021861/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1/1250000000 : ℝ)*X 0 0+(-1178213281/2500000000 : ℝ)*X 0 1+(6642702133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((9903841/31250000 : ℝ)*X 1 0+(4588118259/10000000000 : ℝ)*X 1 1+(1125720263/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3357710087/5000000000 : ℝ)*X 2 0+(-534991487/2000000000 : ℝ)*X 2 1+(-1302303977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4133192781/5000000000 : ℝ)*X 0 0+(-75765729/5000000000 : ℝ)*X 0 1+(2744199891/10000000000 : ℝ)*X 0 2+(4133192781/5000000000 : ℝ)*X 1 0+(-75765729/5000000000 : ℝ)*X 1 1+(2744199891/10000000000 : ℝ)*X 1 2+(4133192781/5000000000 : ℝ)*X 2 0+(-75765729/5000000000 : ℝ)*X 2 1+(2744199891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-93162523/2000000000 : ℝ)*X 0 0+(-101323261/125000000 : ℝ)*X 0 1+(345402093/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((6583734401/10000000000 : ℝ)*X 1 0+(783646207/2500000000 : ℝ)*X 1 1+(573117839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2295711773/10000000000 : ℝ)*X 2 0+(-3309056869/5000000000 : ℝ)*X 2 1+(-3090639359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8121032821/10000000000 : ℝ)*X 0 0+(499/10000000000 : ℝ)*X 0 1+(373978359/1250000000 : ℝ)*X 0 2+(8121032821/10000000000 : ℝ)*X 1 0+(499/10000000000 : ℝ)*X 1 1+(373978359/1250000000 : ℝ)*X 1 2+(8121032821/10000000000 : ℝ)*X 2 0+(499/10000000000 : ℝ)*X 2 1+(373978359/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2293/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2293/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40355404958647904679/7812500000000000000000000 : ℝ) := by norm_num
    linear_combination (398192385537/1000000000000 : ℝ)*(base3) + (1174162347079/1000000000000 : ℝ)*(base7) + (75853/125000000000 : ℝ)*(base40) + (57423674243/200000000000 : ℝ)*(base50) + (66888896537/31250000000 : ℝ)*(major_s0_0) + (66888896537/31250000000 : ℝ)*(major_s0_1) + (66888896537/31250000000 : ℝ)*(major_s0_2) + (4007209/1000000000000 : ℝ)*(sp_s0_0) + (1266812833399/500000000000 : ℝ)*(sp_s0_7) + (1465901068567/500000000000 : ℝ)*(sp_s0_8) + (1266811377287/500000000000 : ℝ)*(sp_s0_9) + (935038327629/500000000000 : ℝ)*(sp_s0_13) + (19922409/1000000000000 : ℝ)*(sp_s0_15) + (6919433/1000000000000 : ℝ)*(sp_s0_23) + (273526673429/250000000000 : ℝ)*(f.failure) + (2533629674007/1000000000000 : ℝ)*(f.sum) + (9080039736113/15625000000000000000000000 : ℝ)*base63 + (12643301895211/312500000000000000000000000 : ℝ)*base65 + (68886086948539/312500000000000000000000000 : ℝ)*base66 + (29292630900351/62500000000000000000000000 : ℝ)*base69 + (79186286104733/156250000000000000000000000 : ℝ)*base71 + (117495236301461/312500000000000000000000000 : ℝ)*base73 + (41179488906601/62500000000000000000000000 : ℝ)*base75 + (7932186587851/62500000000000000000000000 : ℝ)*base77 + (8093721597083/19531250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (4493/12500000000000000 : ℝ)*base87 + (4493/12500000000000000 : ℝ)*base89 + (4493/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25303/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-25303/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13035289901415593602269/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422256949453/500000000000 : ℝ)*(base7) + (150854200423/250000000000 : ℝ)*(base40) + (1286971/500000000000 : ℝ)*(base49) + (79371/250000000000 : ℝ)*(base53) + (139303759667/1000000000000 : ℝ)*(base59) + (22095838427/10000000000 : ℝ)*(major_s0_0) + (22095838427/10000000000 : ℝ)*(major_s0_1) + (2209583525217/1000000000000 : ℝ)*(major_s0_2) + (6145377/250000000000 : ℝ)*(sp_s0_1) + (2819940114987/1000000000000 : ℝ)*(sp_s0_14) + (2819915533479/1000000000000 : ℝ)*(sp_s0_15) + (281994043247/100000000000 : ℝ)*(sp_s0_16) + (1973819673011/1000000000000 : ℝ)*(sp_s0_20) + (70995989/500000000000 : ℝ)*(sp_s0_27) + (282361941521/250000000000 : ℝ)*(f.failure) + (281994043247/100000000000 : ℝ)*(f.sum) + (4513498491155604591/2000000000000000000000000000 : ℝ)*base63 + (876641351915999/10000000000000000000000000000 : ℝ)*base64 + (25900082479131/100000000000000000000000000 : ℝ)*base67 + (1054162554672491/2000000000000000000000000000 : ℝ)*base69 + (6509842176255499/10000000000000000000000000000 : ℝ)*base70 + (56119402789131/100000000000000000000000000 : ℝ)*base73 + (14040762201321/20000000000000000000000000 : ℝ)*base75 + (38410933321/20000000000000000000000000 : ℝ)*base77 + (6964460174131/50000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (9657/12500000000000000 : ℝ)*base87 + (9657/12500000000000000 : ℝ)*base89 + (2843/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16809/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16809/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (76190603522507553884031/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9031817593/1000000000000 : ℝ)*(base3) + (121306839751/100000000000 : ℝ)*(base7) + (5250159/1000000000000 : ℝ)*(base34) + (42498763719/200000000000 : ℝ)*(base40) + (2281983/250000000000 : ℝ)*(base43) + (3701290851/31250000000 : ℝ)*(base50) + (114048414899/62500000000 : ℝ)*(major_s0_0) + (456192690153/250000000000 : ℝ)*(major_s0_1) + (1824779888543/1000000000000 : ℝ)*(major_s0_2) + (10281933/500000000000 : ℝ)*(sp_s0_2) + (1020997421739/500000000000 : ℝ)*(sp_s0_21) + (1025520519581/500000000000 : ℝ)*(sp_s0_22) + (2041979529771/1000000000000 : ℝ)*(sp_s0_23) + (1068391624207/500000000000 : ℝ)*(sp_s0_27) + (14574248729/15625000000 : ℝ)*(f.failure) + (2042009221569/1000000000000 : ℝ)*(f.sum) + (195860409946387/400000000000000000000000000 : ℝ)*base62 + (7760364372354721/10000000000000000000000000000 : ℝ)*base64 + (907002883805609/2500000000000000000000000000 : ℝ)*base67 + (911643806556011/2000000000000000000000000000 : ℝ)*base68 + (3827770838859439/10000000000000000000000000000 : ℝ)*base71 + (382690401127853/625000000000000000000000000 : ℝ)*base72 + (351129436743981/500000000000000000000000000 : ℝ)*base74 + (12167385759823/125000000000000000000000000 : ℝ)*base76 + (360456563955803/2500000000000000000000000000 : ℝ)*base78 + (1497/3125000000000000 : ℝ)*base87 + (407/781250000000000 : ℝ)*base88 + (1497/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (2293/4000 : ℝ) ^ (83/16 : ℝ) ≤ (5577117942955949637/100000000000000000000 : ℝ) := by
    have hpowers : (2293/4000 : ℝ)^83 ≤ (5577117942955949637/100000000000000000000 : ℝ)^16 := by
      have hnat : (2293 : ℕ)^83*100000000000000000000^16 ≤ 5577117942955949637^16*4000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2293 4000 5577117942955949637 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2293/4000 : ℝ)) (X := (5577117942955949637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105577117942955949637/100000000000000000000 : ℝ) ≤ (631573055613091/625000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (105577117942955949637/100000000000000000000 : ℝ)^16 ≤ (631573055613091/625000000000000 : ℝ)^83 := by
      have hnat : (105577117942955949637 : ℕ)^16*625000000000000^83 ≤ 631573055613091^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105577117942955949637 100000000000000000000 631573055613091 625000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631573055613091/625000000000000 : ℝ)) (X := (105577117942955949637/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55577117942955949637/50000000000000000000 : ℝ) ≤ (2551486159611181/2500000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (55577117942955949637/50000000000000000000 : ℝ)^16 ≤ (2551486159611181/2500000000000000 : ℝ)^83 := by
      have hnat : (55577117942955949637 : ℕ)^16*2500000000000000^83 ≤ 2551486159611181^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55577117942955949637 50000000000000000000 2551486159611181 2500000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2551486159611181/2500000000000000 : ℝ)) (X := (55577117942955949637/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6573055613091/358281250000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(25193937158817/1433125000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (2293/4000 : ℝ)) (alpha := (6573055613091/358281250000000 : ℝ)) (beta := (25193937158817/1433125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2293/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6573055613091/358281250000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(25193937158817/1433125000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (25303/50000 : ℝ) ^ (83/16 : ℝ) ≤ (2921110143936901521/100000000000000000000 : ℝ) := by
    have hpowers : (25303/50000 : ℝ)^83 ≤ (2921110143936901521/100000000000000000000 : ℝ)^16 := by
      have hnat : (25303 : ℕ)^83*100000000000000000000^16 ≤ 2921110143936901521^16*50000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25303 50000 2921110143936901521 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25303/50000 : ℝ)) (X := (2921110143936901521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (102921110143936901521/100000000000000000000 : ℝ) ≤ (1005565810266907/1000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (102921110143936901521/100000000000000000000 : ℝ)^16 ≤ (1005565810266907/1000000000000000 : ℝ)^83 := by
      have hnat : (102921110143936901521 : ℕ)^16*1000000000000000^83 ≤ 1005565810266907^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102921110143936901521 100000000000000000000 1005565810266907 1000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005565810266907/1000000000000000 : ℝ)) (X := (102921110143936901521/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (52921110143936901521/50000000000000000000 : ℝ) ≤ (10110055295617229/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (52921110143936901521/50000000000000000000 : ℝ)^16 ≤ (10110055295617229/10000000000000000 : ℝ)^83 := by
      have hnat : (52921110143936901521 : ℕ)^16*10000000000000000^83 ≤ 10110055295617229^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52921110143936901521 50000000000000000000 10110055295617229 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10110055295617229/10000000000000000 : ℝ)) (X := (52921110143936901521/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5565810266907/506060000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(54397192948159/5060600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (25303/50000 : ℝ)) (alpha := (5565810266907/506060000000000 : ℝ)) (beta := (54397192948159/5060600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (25303/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5565810266907/506060000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(54397192948159/5060600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16809/25000 : ℝ) ^ (83/16 : ℝ) ≤ (398597632274766887/3125000000000000000 : ℝ) := by
    have hpowers : (16809/25000 : ℝ)^83 ≤ (398597632274766887/3125000000000000000 : ℝ)^16 := by
      have hnat : (16809 : ℕ)^83*3125000000000000000^16 ≤ 398597632274766887^16*25000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16809 25000 398597632274766887 3125000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16809/25000 : ℝ)) (X := (398597632274766887/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3523597632274766887/3125000000000000000 : ℝ) ≤ (10234116789394043/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3523597632274766887/3125000000000000000 : ℝ)^16 ≤ (10234116789394043/10000000000000000 : ℝ)^83 := by
      have hnat : (3523597632274766887 : ℕ)^16*10000000000000000^83 ≤ 10234116789394043^83*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523597632274766887 3125000000000000000 10234116789394043 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10234116789394043/10000000000000000 : ℝ)) (X := (3523597632274766887/3125000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1961097632274766887/1562500000000000000 : ℝ) ≤ (10447743320145413/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (1961097632274766887/1562500000000000000 : ℝ)^16 ≤ (10447743320145413/10000000000000000 : ℝ)^83 := by
      have hnat : (1961097632274766887 : ℕ)^16*10000000000000000^83 ≤ 10447743320145413^83*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1961097632274766887 1562500000000000000 10447743320145413 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10447743320145413/10000000000000000 : ℝ)) (X := (1961097632274766887/1562500000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(234116789394043/6723600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7120884358379/224120000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (16809/25000 : ℝ)) (alpha := (234116789394043/6723600000000000 : ℝ)) (beta := (7120884358379/224120000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16809/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(234116789394043/6723600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7120884358379/224120000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1725472341/10000000000 : ℝ)*X 0 0+(-50037011/100000000 : ℝ)*X 0 1+(41523783/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4940045709/10000000000 : ℝ)*X 1 0+(1974374921/5000000000 : ℝ)*X 1 1+(26985761/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((38624303/80000000 : ℝ)*X 2 0+(-4046597059/10000000000 : ℝ)*X 2 1+(-848368333/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1502793267/2500000000 : ℝ)*X 0 0+(-83674991/500000000 : ℝ)*X 0 1+(4316486629/10000000000 : ℝ)*X 0 2+(1502793267/2500000000 : ℝ)*X 1 0+(-83674991/500000000 : ℝ)*X 1 1+(4316486629/10000000000 : ℝ)*X 1 2+(1502793267/2500000000 : ℝ)*X 2 0+(-83674991/500000000 : ℝ)*X 2 1+(4316486629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323047_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-555257568455961152949711188287/64238395000000000000000000000 : ℝ) := by norm_num
    linear_combination (90127/1000000000000 : ℝ)*(base5) + (88201/1000000000000 : ℝ)*(base10) + (61131/200000000000 : ℝ)*(base21) + (7673/1000000000000 : ℝ)*(base39) + (73397449881/125000000000 : ℝ)*(base40) + (14331749939/1000000000000 : ℝ)*(base50) + (285148483483/1000000000000 : ℝ)*(base59) + (11097/500000000000 : ℝ)*(base60) + (97817/50000 : ℝ)*(major_s1_0) + (97817/50000 : ℝ)*(major_s1_1) + (97817/50000 : ℝ)*(major_s1_2) + (2881234042131/1000000000000 : ℝ)*(sp_s1_0) + (720308532583/250000000000 : ℝ)*(sp_s1_1) + (720308478701/250000000000 : ℝ)*(sp_s1_2) + (999999909873/1000000000000 : ℝ)*(sp_s1_6) + (720308532583/250000000000 : ℝ)*(f.sum) + (2014526359759010989/4253181270000000000000000000000 : ℝ)*base63 + (294160646539/700375000000000000000000 : ℝ)*base64 + (26277631731683/253030000000000000000000000 : ℝ)*base66 + (7458000331829/21011250000000000000000000 : ℝ)*base69 + (23276645821692109/32119197500000000000000000000 : ℝ)*base70 + (10610975798219/22930000000000000000000000 : ℝ)*base73 + (11594013433099/31628750000000000000000000 : ℝ)*base74 + (521306843659/2866250000000000000000000 : ℝ)*base76 + (362749002630102769/580197790000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p023_b025 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=47 := by omega
  rcases hc with rfl
  · exact collision_c323047 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 47 ≤ c.val) (hhi : c.val < 48)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
