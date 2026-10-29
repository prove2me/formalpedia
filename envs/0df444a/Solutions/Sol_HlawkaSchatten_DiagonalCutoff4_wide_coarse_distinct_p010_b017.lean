-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:37.848471+00:00
-- url     : https://prove2.me/submissions/67117830-8227-4f75-9f19-a3d86ac1bcb9

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
theorem collision_support_c310029_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-991954481/2500000000 : ℝ)*x 0 + (9612243/25000000 : ℝ)*x 1 + (985829859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991954481/2500000000 : ℝ)^9 ≤ (6093716230371/20000000000000 : ℝ)^7 := by
    have hnat : (991954481 : ℕ)^9*20000000000000^7 ≤ 6093716230371^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991954481 2500000000 6093716230371 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9612243/25000000 : ℝ)^9 ≤ (29260407532109/100000000000000 : ℝ)^7 := by
    have hnat : (9612243 : ℕ)^9*100000000000000^7 ≤ 29260407532109^7*25000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9612243 25000000 29260407532109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985829859/2000000000 : ℝ)^9 ≤ (20135505648709/50000000000000 : ℝ)^7 := by
    have hnat : (985829859 : ℕ)^9*50000000000000^7 ≤ 20135505648709^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985829859 2000000000 20135505648709 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-991954481/2500000000 : ℝ), (9612243/25000000 : ℝ), (985829859/2000000000 : ℝ)] ![(6093716230371/20000000000000 : ℝ), (29260407532109/100000000000000 : ℝ), (20135505648709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-991954481/2500000000 : ℝ)|^9 ≤ (6093716230371/20000000000000 : ℝ)^7
        have hw : |(-991954481/2500000000 : ℝ)|=(991954481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9612243/25000000 : ℝ)|^9 ≤ (29260407532109/100000000000000 : ℝ)^7
        have hw : |(9612243/25000000 : ℝ)|=(9612243/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(985829859/2000000000 : ℝ)|^9 ≤ (20135505648709/50000000000000 : ℝ)^7
        have hw : |(985829859/2000000000 : ℝ)|=(985829859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3053303413/5000000000 : ℝ)*x 0 + (-1018491751/10000000000 : ℝ)*x 1 + (5060643929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3053303413/5000000000 : ℝ)^9 ≤ (53039564206007/100000000000000 : ℝ)^7 := by
    have hnat : (3053303413 : ℕ)^9*100000000000000^7 ≤ 53039564206007^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3053303413 5000000000 53039564206007 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018491751/10000000000 : ℝ)^9 ≤ (5302941133439/100000000000000 : ℝ)^7 := by
    have hnat : (1018491751 : ℕ)^9*100000000000000^7 ≤ 5302941133439^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018491751 10000000000 5302941133439 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5060643929/10000000000 : ℝ)^9 ≤ (41657494638327/100000000000000 : ℝ)^7 := by
    have hnat : (5060643929 : ℕ)^9*100000000000000^7 ≤ 41657494638327^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060643929 10000000000 41657494638327 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3053303413/5000000000 : ℝ), (-1018491751/10000000000 : ℝ), (5060643929/10000000000 : ℝ)] ![(53039564206007/100000000000000 : ℝ), (5302941133439/100000000000000 : ℝ), (41657494638327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3053303413/5000000000 : ℝ)|^9 ≤ (53039564206007/100000000000000 : ℝ)^7
        have hw : |(3053303413/5000000000 : ℝ)|=(3053303413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018491751/10000000000 : ℝ)|^9 ≤ (5302941133439/100000000000000 : ℝ)^7
        have hw : |(-1018491751/10000000000 : ℝ)|=(1018491751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5060643929/10000000000 : ℝ)|^9 ≤ (41657494638327/100000000000000 : ℝ)^7
        have hw : |(5060643929/10000000000 : ℝ)|=(5060643929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (477148971/2500000000 : ℝ)*x 0 + (7778156117/10000000000 : ℝ)*x 1 + (-2371014557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477148971/2500000000 : ℝ)^9 ≤ (11890597881683/100000000000000 : ℝ)^7 := by
    have hnat : (477148971 : ℕ)^9*100000000000000^7 ≤ 11890597881683^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477148971 2500000000 11890597881683 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7778156117/10000000000 : ℝ)^9 ≤ (14478666109083/20000000000000 : ℝ)^7 := by
    have hnat : (7778156117 : ℕ)^9*20000000000000^7 ≤ 14478666109083^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7778156117 10000000000 14478666109083 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371014557/10000000000 : ℝ)^9 ≤ (3143214311969/20000000000000 : ℝ)^7 := by
    have hnat : (2371014557 : ℕ)^9*20000000000000^7 ≤ 3143214311969^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371014557 10000000000 3143214311969 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(477148971/2500000000 : ℝ), (7778156117/10000000000 : ℝ), (-2371014557/10000000000 : ℝ)] ![(11890597881683/100000000000000 : ℝ), (14478666109083/20000000000000 : ℝ), (3143214311969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(477148971/2500000000 : ℝ)|^9 ≤ (11890597881683/100000000000000 : ℝ)^7
        have hw : |(477148971/2500000000 : ℝ)|=(477148971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7778156117/10000000000 : ℝ)|^9 ≤ (14478666109083/20000000000000 : ℝ)^7
        have hw : |(7778156117/10000000000 : ℝ)|=(7778156117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2371014557/10000000000 : ℝ)|^9 ≤ (3143214311969/20000000000000 : ℝ)^7
        have hw : |(-2371014557/10000000000 : ℝ)|=(2371014557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^9 ≤ (1 : ℝ)^7 := by
    have hnat : (1 : ℕ)^9*1^7 ≤ 1^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^9 ≤ (0 : ℝ)^7 := by
    have hnat : (0 : ℕ)^9*1^7 ≤ 0^7*1^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^9 ≤ (1 : ℝ)^7
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^9 ≤ (0 : ℝ)^7
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-262813799/625000000 : ℝ)*x 0 + (1437151961/5000000000 : ℝ)*x 1 + (1112465003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262813799/625000000 : ℝ)^9 ≤ (256485821183/781250000000 : ℝ)^7 := by
    have hnat : (262813799 : ℕ)^9*781250000000^7 ≤ 256485821183^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262813799 625000000 256485821183 781250000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1437151961/5000000000 : ℝ)^9 ≤ (10064628414307/50000000000000 : ℝ)^7 := by
    have hnat : (1437151961 : ℕ)^9*50000000000000^7 ≤ 10064628414307^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437151961 5000000000 10064628414307 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112465003/2000000000 : ℝ)^9 ≤ (940811160779/2000000000000 : ℝ)^7 := by
    have hnat : (1112465003 : ℕ)^9*2000000000000^7 ≤ 940811160779^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112465003 2000000000 940811160779 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262813799/625000000 : ℝ), (1437151961/5000000000 : ℝ), (1112465003/2000000000 : ℝ)] ![(256485821183/781250000000 : ℝ), (10064628414307/50000000000000 : ℝ), (940811160779/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262813799/625000000 : ℝ)|^9 ≤ (256485821183/781250000000 : ℝ)^7
        have hw : |(-262813799/625000000 : ℝ)|=(262813799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1437151961/5000000000 : ℝ)|^9 ≤ (10064628414307/50000000000000 : ℝ)^7
        have hw : |(1437151961/5000000000 : ℝ)|=(1437151961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112465003/2000000000 : ℝ)|^9 ≤ (940811160779/2000000000000 : ℝ)^7
        have hw : |(1112465003/2000000000 : ℝ)|=(1112465003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5514365639/10000000000 : ℝ)*x 0 + (-267072037/10000000000 : ℝ)*x 1 + (6061075663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514365639/10000000000 : ℝ)^9 ≤ (46519725960017/100000000000000 : ℝ)^7 := by
    have hnat : (5514365639 : ℕ)^9*100000000000000^7 ≤ 46519725960017^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514365639 10000000000 46519725960017 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267072037/10000000000 : ℝ)^9 ≤ (94862306813/10000000000000 : ℝ)^7 := by
    have hnat : (267072037 : ℕ)^9*10000000000000^7 ≤ 94862306813^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267072037 10000000000 94862306813 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6061075663/10000000000 : ℝ)^9 ≤ (13132912739353/25000000000000 : ℝ)^7 := by
    have hnat : (6061075663 : ℕ)^9*25000000000000^7 ≤ 13132912739353^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6061075663 10000000000 13132912739353 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514365639/10000000000 : ℝ), (-267072037/10000000000 : ℝ), (6061075663/10000000000 : ℝ)] ![(46519725960017/100000000000000 : ℝ), (94862306813/10000000000000 : ℝ), (13132912739353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514365639/10000000000 : ℝ)|^9 ≤ (46519725960017/100000000000000 : ℝ)^7
        have hw : |(5514365639/10000000000 : ℝ)|=(5514365639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267072037/10000000000 : ℝ)|^9 ≤ (94862306813/10000000000000 : ℝ)^7
        have hw : |(-267072037/10000000000 : ℝ)|=(267072037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6061075663/10000000000 : ℝ)|^9 ≤ (13132912739353/25000000000000 : ℝ)^7
        have hw : |(6061075663/10000000000 : ℝ)|=(6061075663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (643049583/10000000000 : ℝ)*x 0 + (9439920731/10000000000 : ℝ)*x 1 + (-850614293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643049583/10000000000 : ℝ)^9 ≤ (366988868431/12500000000000 : ℝ)^7 := by
    have hnat : (643049583 : ℕ)^9*12500000000000^7 ≤ 366988868431^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643049583 10000000000 366988868431 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9439920731/10000000000 : ℝ)^9 ≤ (46428692242309/50000000000000 : ℝ)^7 := by
    have hnat : (9439920731 : ℕ)^9*50000000000000^7 ≤ 46428692242309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9439920731 10000000000 46428692242309 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850614293/10000000000 : ℝ)^9 ≤ (131459517403/3125000000000 : ℝ)^7 := by
    have hnat : (850614293 : ℕ)^9*3125000000000^7 ≤ 131459517403^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850614293 10000000000 131459517403 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(643049583/10000000000 : ℝ), (9439920731/10000000000 : ℝ), (-850614293/10000000000 : ℝ)] ![(366988868431/12500000000000 : ℝ), (46428692242309/50000000000000 : ℝ), (131459517403/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(643049583/10000000000 : ℝ)|^9 ≤ (366988868431/12500000000000 : ℝ)^7
        have hw : |(643049583/10000000000 : ℝ)|=(643049583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9439920731/10000000000 : ℝ)|^9 ≤ (46428692242309/50000000000000 : ℝ)^7
        have hw : |(9439920731/10000000000 : ℝ)|=(9439920731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-850614293/10000000000 : ℝ)|^9 ≤ (131459517403/3125000000000 : ℝ)^7
        have hw : |(-850614293/10000000000 : ℝ)|=(850614293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (406539371/1000000000 : ℝ)*x 0 + (2114291291/5000000000 : ℝ)*x 1 + (2234224251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406539371/1000000000 : ℝ)^9 ≤ (31435302404223/100000000000000 : ℝ)^7 := by
    have hnat : (406539371 : ℕ)^9*100000000000000^7 ≤ 31435302404223^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406539371 1000000000 31435302404223 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114291291/5000000000 : ℝ)^9 ≤ (33066888850701/100000000000000 : ℝ)^7 := by
    have hnat : (2114291291 : ℕ)^9*100000000000000^7 ≤ 33066888850701^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114291291 5000000000 33066888850701 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234224251/5000000000 : ℝ)^9 ≤ (35497808721109/100000000000000 : ℝ)^7 := by
    have hnat : (2234224251 : ℕ)^9*100000000000000^7 ≤ 35497808721109^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234224251 5000000000 35497808721109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(406539371/1000000000 : ℝ), (2114291291/5000000000 : ℝ), (2234224251/5000000000 : ℝ)] ![(31435302404223/100000000000000 : ℝ), (33066888850701/100000000000000 : ℝ), (35497808721109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(406539371/1000000000 : ℝ)|^9 ≤ (31435302404223/100000000000000 : ℝ)^7
        have hw : |(406539371/1000000000 : ℝ)|=(406539371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114291291/5000000000 : ℝ)|^9 ≤ (33066888850701/100000000000000 : ℝ)^7
        have hw : |(2114291291/5000000000 : ℝ)|=(2114291291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2234224251/5000000000 : ℝ)|^9 ≤ (35497808721109/100000000000000 : ℝ)^7
        have hw : |(2234224251/5000000000 : ℝ)|=(2234224251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2381223727/5000000000 : ℝ)*x 0 + (1279355357/5000000000 : ℝ)*x 1 + (264675679/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2381223727/5000000000 : ℝ)^9 ≤ (9632115696379/25000000000000 : ℝ)^7 := by
    have hnat : (2381223727 : ℕ)^9*25000000000000^7 ≤ 9632115696379^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2381223727 5000000000 9632115696379 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279355357/5000000000 : ℝ)^9 ≤ (3466684987623/20000000000000 : ℝ)^7 := by
    have hnat : (1279355357 : ℕ)^9*20000000000000^7 ≤ 3466684987623^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279355357 5000000000 3466684987623 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264675679/500000000 : ℝ)^9 ≤ (2758632015927/6250000000000 : ℝ)^7 := by
    have hnat : (264675679 : ℕ)^9*6250000000000^7 ≤ 2758632015927^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264675679 500000000 2758632015927 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2381223727/5000000000 : ℝ), (1279355357/5000000000 : ℝ), (264675679/500000000 : ℝ)] ![(9632115696379/25000000000000 : ℝ), (3466684987623/20000000000000 : ℝ), (2758632015927/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2381223727/5000000000 : ℝ)|^9 ≤ (9632115696379/25000000000000 : ℝ)^7
        have hw : |(-2381223727/5000000000 : ℝ)|=(2381223727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1279355357/5000000000 : ℝ)|^9 ≤ (3466684987623/20000000000000 : ℝ)^7
        have hw : |(1279355357/5000000000 : ℝ)|=(1279355357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264675679/500000000 : ℝ)|^9 ≤ (2758632015927/6250000000000 : ℝ)^7
        have hw : |(264675679/500000000 : ℝ)|=(264675679/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (361394273/500000000 : ℝ)*x 0 + (-1216243171/10000000000 : ℝ)*x 1 + (114368599/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361394273/500000000 : ℝ)^9 ≤ (32938117113437/50000000000000 : ℝ)^7 := by
    have hnat : (361394273 : ℕ)^9*50000000000000^7 ≤ 32938117113437^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361394273 500000000 32938117113437 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216243171/10000000000 : ℝ)^9 ≤ (3330946677729/50000000000000 : ℝ)^7 := by
    have hnat : (1216243171 : ℕ)^9*50000000000000^7 ≤ 3330946677729^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216243171 10000000000 3330946677729 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114368599/312500000 : ℝ)^9 ≤ (27461872404203/100000000000000 : ℝ)^7 := by
    have hnat : (114368599 : ℕ)^9*100000000000000^7 ≤ 27461872404203^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114368599 312500000 27461872404203 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(361394273/500000000 : ℝ), (-1216243171/10000000000 : ℝ), (114368599/312500000 : ℝ)] ![(32938117113437/50000000000000 : ℝ), (3330946677729/50000000000000 : ℝ), (27461872404203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(361394273/500000000 : ℝ)|^9 ≤ (32938117113437/50000000000000 : ℝ)^7
        have hw : |(361394273/500000000 : ℝ)|=(361394273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1216243171/10000000000 : ℝ)|^9 ≤ (3330946677729/50000000000000 : ℝ)^7
        have hw : |(-1216243171/10000000000 : ℝ)|=(1216243171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114368599/312500000 : ℝ)|^9 ≤ (27461872404203/100000000000000 : ℝ)^7
        have hw : |(114368599/312500000 : ℝ)|=(114368599/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1231546821/10000000000 : ℝ)*x 0 + (7927487287/10000000000 : ℝ)*x 1 + (-2753144203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1231546821/10000000000 : ℝ)^9 ≤ (3384930594961/50000000000000 : ℝ)^7 := by
    have hnat : (1231546821 : ℕ)^9*50000000000000^7 ≤ 3384930594961^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231546821 10000000000 3384930594961 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7927487287/10000000000 : ℝ)^9 ≤ (37092588837117/50000000000000 : ℝ)^7 := by
    have hnat : (7927487287 : ℕ)^9*50000000000000^7 ≤ 37092588837117^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7927487287 10000000000 37092588837117 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753144203/10000000000 : ℝ)^9 ≤ (19044961124749/100000000000000 : ℝ)^7 := by
    have hnat : (2753144203 : ℕ)^9*100000000000000^7 ≤ 19044961124749^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753144203 10000000000 19044961124749 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1231546821/10000000000 : ℝ), (7927487287/10000000000 : ℝ), (-2753144203/10000000000 : ℝ)] ![(3384930594961/50000000000000 : ℝ), (37092588837117/50000000000000 : ℝ), (19044961124749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1231546821/10000000000 : ℝ)|^9 ≤ (3384930594961/50000000000000 : ℝ)^7
        have hw : |(1231546821/10000000000 : ℝ)|=(1231546821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7927487287/10000000000 : ℝ)|^9 ≤ (37092588837117/50000000000000 : ℝ)^7
        have hw : |(7927487287/10000000000 : ℝ)|=(7927487287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2753144203/10000000000 : ℝ)|^9 ≤ (19044961124749/100000000000000 : ℝ)^7
        have hw : |(-2753144203/10000000000 : ℝ)|=(2753144203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2796327613/10000000000 : ℝ)*x 0 + (3576184927/10000000000 : ℝ)*x 1 + (6184609933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2796327613/10000000000 : ℝ)^9 ≤ (4857472608701/25000000000000 : ℝ)^7 := by
    have hnat : (2796327613 : ℕ)^9*25000000000000^7 ≤ 4857472608701^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796327613 10000000000 4857472608701 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3576184927/10000000000 : ℝ)^9 ≤ (13328941993779/50000000000000 : ℝ)^7 := by
    have hnat : (3576184927 : ℕ)^9*50000000000000^7 ≤ 13328941993779^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576184927 10000000000 13328941993779 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6184609933/10000000000 : ℝ)^9 ≤ (26956112778937/50000000000000 : ℝ)^7 := by
    have hnat : (6184609933 : ℕ)^9*50000000000000^7 ≤ 26956112778937^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6184609933 10000000000 26956112778937 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2796327613/10000000000 : ℝ), (3576184927/10000000000 : ℝ), (6184609933/10000000000 : ℝ)] ![(4857472608701/25000000000000 : ℝ), (13328941993779/50000000000000 : ℝ), (26956112778937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2796327613/10000000000 : ℝ)|^9 ≤ (4857472608701/25000000000000 : ℝ)^7
        have hw : |(2796327613/10000000000 : ℝ)|=(2796327613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3576184927/10000000000 : ℝ)|^9 ≤ (13328941993779/50000000000000 : ℝ)^7
        have hw : |(3576184927/10000000000 : ℝ)|=(3576184927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6184609933/10000000000 : ℝ)|^9 ≤ (26956112778937/50000000000000 : ℝ)^7
        have hw : |(6184609933/10000000000 : ℝ)|=(6184609933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2984179137/10000000000 : ℝ)*x 0 + (772435877/2000000000 : ℝ)*x 1 + (2891179723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2984179137/10000000000 : ℝ)^9 ≤ (105619683721/500000000000 : ℝ)^7 := by
    have hnat : (2984179137 : ℕ)^9*500000000000^7 ≤ 105619683721^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2984179137 10000000000 105619683721 500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772435877/2000000000 : ℝ)^9 ≤ (3678701763591/12500000000000 : ℝ)^7 := by
    have hnat : (772435877 : ℕ)^9*12500000000000^7 ≤ 3678701763591^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772435877 2000000000 3678701763591 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2891179723/5000000000 : ℝ)^9 ≤ (9889289825803/20000000000000 : ℝ)^7 := by
    have hnat : (2891179723 : ℕ)^9*20000000000000^7 ≤ 9889289825803^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891179723 5000000000 9889289825803 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2984179137/10000000000 : ℝ), (772435877/2000000000 : ℝ), (2891179723/5000000000 : ℝ)] ![(105619683721/500000000000 : ℝ), (3678701763591/12500000000000 : ℝ), (9889289825803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2984179137/10000000000 : ℝ)|^9 ≤ (105619683721/500000000000 : ℝ)^7
        have hw : |(-2984179137/10000000000 : ℝ)|=(2984179137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772435877/2000000000 : ℝ)|^9 ≤ (3678701763591/12500000000000 : ℝ)^7
        have hw : |(772435877/2000000000 : ℝ)|=(772435877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2891179723/5000000000 : ℝ)|^9 ≤ (9889289825803/20000000000000 : ℝ)^7
        have hw : |(2891179723/5000000000 : ℝ)|=(2891179723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7801708553/10000000000 : ℝ)*x 0 + (-260320767/10000000000 : ℝ)*x 1 + (709991963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7801708553/10000000000 : ℝ)^9 ≤ (18168823024353/25000000000000 : ℝ)^7 := by
    have hnat : (7801708553 : ℕ)^9*25000000000000^7 ≤ 18168823024353^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7801708553 10000000000 18168823024353 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260320767/10000000000 : ℝ)^9 ≤ (458951773517/50000000000000 : ℝ)^7 := by
    have hnat : (260320767 : ℕ)^9*50000000000000^7 ≤ 458951773517^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260320767 10000000000 458951773517 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709991963/2000000000 : ℝ)^9 ≤ (660170108373/2500000000000 : ℝ)^7 := by
    have hnat : (709991963 : ℕ)^9*2500000000000^7 ≤ 660170108373^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709991963 2000000000 660170108373 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7801708553/10000000000 : ℝ), (-260320767/10000000000 : ℝ), (709991963/2000000000 : ℝ)] ![(18168823024353/25000000000000 : ℝ), (458951773517/50000000000000 : ℝ), (660170108373/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7801708553/10000000000 : ℝ)|^9 ≤ (18168823024353/25000000000000 : ℝ)^7
        have hw : |(7801708553/10000000000 : ℝ)|=(7801708553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260320767/10000000000 : ℝ)|^9 ≤ (458951773517/50000000000000 : ℝ)^7
        have hw : |(-260320767/10000000000 : ℝ)|=(260320767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709991963/2000000000 : ℝ)|^9 ≤ (660170108373/2500000000000 : ℝ)^7
        have hw : |(709991963/2000000000 : ℝ)|=(709991963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (644224789/10000000000 : ℝ)*x 0 + (4613319013/5000000000 : ℝ)*x 1 + (-1248296139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (644224789/10000000000 : ℝ)^9 ≤ (2942811282961/100000000000000 : ℝ)^7 := by
    have hnat : (644224789 : ℕ)^9*100000000000000^7 ≤ 2942811282961^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644224789 10000000000 2942811282961 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4613319013/5000000000 : ℝ)^9 ≤ (90168720419619/100000000000000 : ℝ)^7 := by
    have hnat : (4613319013 : ℕ)^9*100000000000000^7 ≤ 90168720419619^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4613319013 5000000000 90168720419619 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248296139/10000000000 : ℝ)^9 ≤ (3444234145379/50000000000000 : ℝ)^7 := by
    have hnat : (1248296139 : ℕ)^9*50000000000000^7 ≤ 3444234145379^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248296139 10000000000 3444234145379 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(644224789/10000000000 : ℝ), (4613319013/5000000000 : ℝ), (-1248296139/10000000000 : ℝ)] ![(2942811282961/100000000000000 : ℝ), (90168720419619/100000000000000 : ℝ), (3444234145379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(644224789/10000000000 : ℝ)|^9 ≤ (2942811282961/100000000000000 : ℝ)^7
        have hw : |(644224789/10000000000 : ℝ)|=(644224789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4613319013/5000000000 : ℝ)|^9 ≤ (90168720419619/100000000000000 : ℝ)^7
        have hw : |(4613319013/5000000000 : ℝ)|=(4613319013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1248296139/10000000000 : ℝ)|^9 ≤ (3444234145379/50000000000000 : ℝ)^7
        have hw : |(-1248296139/10000000000 : ℝ)|=(1248296139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6802472713/10000000000 : ℝ)*x 0 + (156987263/625000000 : ℝ)*x 1 + (3095284143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6802472713/10000000000 : ℝ)^9 ≤ (15233417107403/25000000000000 : ℝ)^7 := by
    have hnat : (6802472713 : ℕ)^9*25000000000000^7 ≤ 15233417107403^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6802472713 10000000000 15233417107403 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156987263/625000000 : ℝ)^9 ≤ (3385176892497/20000000000000 : ℝ)^7 := by
    have hnat : (156987263 : ℕ)^9*20000000000000^7 ≤ 3385176892497^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156987263 625000000 3385176892497 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3095284143/10000000000 : ℝ)^9 ≤ (5535111772771/25000000000000 : ℝ)^7 := by
    have hnat : (3095284143 : ℕ)^9*25000000000000^7 ≤ 5535111772771^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3095284143 10000000000 5535111772771 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6802472713/10000000000 : ℝ), (156987263/625000000 : ℝ), (3095284143/10000000000 : ℝ)] ![(15233417107403/25000000000000 : ℝ), (3385176892497/20000000000000 : ℝ), (5535111772771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6802472713/10000000000 : ℝ)|^9 ≤ (15233417107403/25000000000000 : ℝ)^7
        have hw : |(6802472713/10000000000 : ℝ)|=(6802472713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156987263/625000000 : ℝ)|^9 ≤ (3385176892497/20000000000000 : ℝ)^7
        have hw : |(156987263/625000000 : ℝ)|=(156987263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3095284143/10000000000 : ℝ)|^9 ≤ (5535111772771/25000000000000 : ℝ)^7
        have hw : |(3095284143/10000000000 : ℝ)|=(3095284143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-507050889/1250000000 : ℝ)*x 0 + (168905859/400000000 : ℝ)*x 1 + (4483028169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507050889/1250000000 : ℝ)^9 ≤ (7836497201971/25000000000000 : ℝ)^7 := by
    have hnat : (507050889 : ℕ)^9*25000000000000^7 ≤ 7836497201971^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507050889 1250000000 7836497201971 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168905859/400000000 : ℝ)^9 ≤ (33007218639337/100000000000000 : ℝ)^7 := by
    have hnat : (168905859 : ℕ)^9*100000000000000^7 ≤ 33007218639337^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168905859 400000000 33007218639337 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483028169/10000000000 : ℝ)^9 ≤ (17823396267697/50000000000000 : ℝ)^7 := by
    have hnat : (4483028169 : ℕ)^9*50000000000000^7 ≤ 17823396267697^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483028169 10000000000 17823396267697 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507050889/1250000000 : ℝ), (168905859/400000000 : ℝ), (4483028169/10000000000 : ℝ)] ![(7836497201971/25000000000000 : ℝ), (33007218639337/100000000000000 : ℝ), (17823396267697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507050889/1250000000 : ℝ)|^9 ≤ (7836497201971/25000000000000 : ℝ)^7
        have hw : |(-507050889/1250000000 : ℝ)|=(507050889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168905859/400000000 : ℝ)|^9 ≤ (33007218639337/100000000000000 : ℝ)^7
        have hw : |(168905859/400000000 : ℝ)|=(168905859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483028169/10000000000 : ℝ)|^9 ≤ (17823396267697/50000000000000 : ℝ)^7
        have hw : |(4483028169/10000000000 : ℝ)|=(4483028169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5383415177/10000000000 : ℝ)*x 0 + (-586246297/2500000000 : ℝ)*x 1 + (969228227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383415177/10000000000 : ℝ)^9 ≤ (45104229391499/100000000000000 : ℝ)^7 := by
    have hnat : (5383415177 : ℕ)^9*100000000000000^7 ≤ 45104229391499^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383415177 10000000000 45104229391499 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586246297/2500000000 : ℝ)^9 ≤ (15494591591351/100000000000000 : ℝ)^7 := by
    have hnat : (586246297 : ℕ)^9*100000000000000^7 ≤ 15494591591351^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586246297 2500000000 15494591591351 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969228227/2000000000 : ℝ)^9 ≤ (39401179004967/100000000000000 : ℝ)^7 := by
    have hnat : (969228227 : ℕ)^9*100000000000000^7 ≤ 39401179004967^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969228227 2000000000 39401179004967 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383415177/10000000000 : ℝ), (-586246297/2500000000 : ℝ), (969228227/2000000000 : ℝ)] ![(45104229391499/100000000000000 : ℝ), (15494591591351/100000000000000 : ℝ), (39401179004967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383415177/10000000000 : ℝ)|^9 ≤ (45104229391499/100000000000000 : ℝ)^7
        have hw : |(5383415177/10000000000 : ℝ)|=(5383415177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-586246297/2500000000 : ℝ)|^9 ≤ (15494591591351/100000000000000 : ℝ)^7
        have hw : |(-586246297/2500000000 : ℝ)|=(586246297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(969228227/2000000000 : ℝ)|^9 ≤ (39401179004967/100000000000000 : ℝ)^7
        have hw : |(969228227/2000000000 : ℝ)|=(969228227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1512976581/5000000000 : ℝ)*x 0 + (1239195581/2000000000 : ℝ)*x 1 + (-1672099581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1512976581/5000000000 : ℝ)^9 ≤ (2688110573203/12500000000000 : ℝ)^7 := by
    have hnat : (1512976581 : ℕ)^9*12500000000000^7 ≤ 2688110573203^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512976581 5000000000 2688110573203 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1239195581/2000000000 : ℝ)^9 ≤ (1080793373507/2000000000000 : ℝ)^7 := by
    have hnat : (1239195581 : ℕ)^9*2000000000000^7 ≤ 1080793373507^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239195581 2000000000 1080793373507 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1672099581/5000000000 : ℝ)^9 ≤ (305693084097/1250000000000 : ℝ)^7 := by
    have hnat : (1672099581 : ℕ)^9*1250000000000^7 ≤ 305693084097^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672099581 5000000000 305693084097 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1512976581/5000000000 : ℝ), (1239195581/2000000000 : ℝ), (-1672099581/5000000000 : ℝ)] ![(2688110573203/12500000000000 : ℝ), (1080793373507/2000000000000 : ℝ), (305693084097/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1512976581/5000000000 : ℝ)|^9 ≤ (2688110573203/12500000000000 : ℝ)^7
        have hw : |(1512976581/5000000000 : ℝ)|=(1512976581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1239195581/2000000000 : ℝ)|^9 ≤ (1080793373507/2000000000000 : ℝ)^7
        have hw : |(1239195581/2000000000 : ℝ)|=(1239195581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1672099581/5000000000 : ℝ)|^9 ≤ (305693084097/1250000000000 : ℝ)^7
        have hw : |(-1672099581/5000000000 : ℝ)|=(1672099581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310029_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2892051/6250000 : ℝ)*x 0 + (3964720993/10000000000 : ℝ)*x 1 + (2082735491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2892051/6250000 : ℝ)^9 ≤ (37128274565609/100000000000000 : ℝ)^7 := by
    have hnat : (2892051 : ℕ)^9*100000000000000^7 ≤ 37128274565609^7*6250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892051 6250000 37128274565609 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3964720993/10000000000 : ℝ)^9 ≤ (30438008855687/100000000000000 : ℝ)^7 := by
    have hnat : (3964720993 : ℕ)^9*100000000000000^7 ≤ 30438008855687^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3964720993 10000000000 30438008855687 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082735491/5000000000 : ℝ)^9 ≤ (32433716570391/100000000000000 : ℝ)^7 := by
    have hnat : (2082735491 : ℕ)^9*100000000000000^7 ≤ 32433716570391^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082735491 5000000000 32433716570391 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2892051/6250000 : ℝ), (3964720993/10000000000 : ℝ), (2082735491/5000000000 : ℝ)] ![(37128274565609/100000000000000 : ℝ), (30438008855687/100000000000000 : ℝ), (32433716570391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2892051/6250000 : ℝ)|^9 ≤ (37128274565609/100000000000000 : ℝ)^7
        have hw : |(2892051/6250000 : ℝ)|=(2892051/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3964720993/10000000000 : ℝ)|^9 ≤ (30438008855687/100000000000000 : ℝ)^7
        have hw : |(3964720993/10000000000 : ℝ)|=(3964720993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2082735491/5000000000 : ℝ)|^9 ≤ (32433716570391/100000000000000 : ℝ)^7
        have hw : |(2082735491/5000000000 : ℝ)|=(2082735491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310029 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-991954481/2500000000 : ℝ)*X 0 0+(9612243/25000000 : ℝ)*X 0 1+(985829859/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3053303413/5000000000 : ℝ)*X 1 0+(-1018491751/10000000000 : ℝ)*X 1 1+(5060643929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((477148971/2500000000 : ℝ)*X 2 0+(7778156117/10000000000 : ℝ)*X 2 1+(-2371014557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-262813799/625000000 : ℝ)*X 0 0+(1437151961/5000000000 : ℝ)*X 0 1+(1112465003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5514365639/10000000000 : ℝ)*X 1 0+(-267072037/10000000000 : ℝ)*X 1 1+(6061075663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((643049583/10000000000 : ℝ)*X 2 0+(9439920731/10000000000 : ℝ)*X 2 1+(-850614293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((406539371/1000000000 : ℝ)*X 0 0+(2114291291/5000000000 : ℝ)*X 0 1+(2234224251/5000000000 : ℝ)*X 0 2+(406539371/1000000000 : ℝ)*X 1 0+(2114291291/5000000000 : ℝ)*X 1 1+(2234224251/5000000000 : ℝ)*X 1 2+(406539371/1000000000 : ℝ)*X 2 0+(2114291291/5000000000 : ℝ)*X 2 1+(2234224251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2381223727/5000000000 : ℝ)*X 0 0+(1279355357/5000000000 : ℝ)*X 0 1+(264675679/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((361394273/500000000 : ℝ)*X 1 0+(-1216243171/10000000000 : ℝ)*X 1 1+(114368599/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1231546821/10000000000 : ℝ)*X 2 0+(7927487287/10000000000 : ℝ)*X 2 1+(-2753144203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2796327613/10000000000 : ℝ)*X 0 0+(3576184927/10000000000 : ℝ)*X 0 1+(6184609933/10000000000 : ℝ)*X 0 2+(2796327613/10000000000 : ℝ)*X 1 0+(3576184927/10000000000 : ℝ)*X 1 1+(6184609933/10000000000 : ℝ)*X 1 2+(2796327613/10000000000 : ℝ)*X 2 0+(3576184927/10000000000 : ℝ)*X 2 1+(6184609933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-2984179137/10000000000 : ℝ)*X 0 0+(772435877/2000000000 : ℝ)*X 0 1+(2891179723/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((7801708553/10000000000 : ℝ)*X 1 0+(-260320767/10000000000 : ℝ)*X 1 1+(709991963/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((644224789/10000000000 : ℝ)*X 2 0+(4613319013/5000000000 : ℝ)*X 2 1+(-1248296139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((6802472713/10000000000 : ℝ)*X 0 0+(156987263/625000000 : ℝ)*X 0 1+(3095284143/10000000000 : ℝ)*X 0 2+(6802472713/10000000000 : ℝ)*X 1 0+(156987263/625000000 : ℝ)*X 1 1+(3095284143/10000000000 : ℝ)*X 1 2+(6802472713/10000000000 : ℝ)*X 2 0+(156987263/625000000 : ℝ)*X 2 1+(3095284143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((10043/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10043/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7648678844947517770293/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (219328943691/500000000000 : ℝ)*(base50) + (577492778779/1000000000000 : ℝ)*(base59) + (634186998933/250000000000 : ℝ)*(major_s0_0) + (2427661127251/500000000000 : ℝ)*(major_s0_1) + (634186998933/250000000000 : ℝ)*(major_s0_2) + (40785711/250000000000 : ℝ)*(sp_s0_0) + (231857425877/100000000000 : ℝ)*(sp_s0_4) + (1752704049561/500000000000 : ℝ)*(sp_s0_7) + (3505593643553/1000000000000 : ℝ)*(sp_s0_8) + (3505237881607/1000000000000 : ℝ)*(sp_s0_9) + (783939286721/500000000000 : ℝ)*(sp_s0_12) + (22401587/1000000000000 : ℝ)*(sp_s0_13) + (9337673/500000000000 : ℝ)*(sp_s0_19) + (177880973/500000000000 : ℝ)*(sp_s0_22) + (391974312197/250000000000 : ℝ)*(f.failure) + (3505593643553/1000000000000 : ℝ)*(f.sum) + (5958010076569/1000000000000000000000000000 : ℝ)*base62 + (182089836950747/2500000000000000000000000000 : ℝ)*base64 + (1357661842988291/5000000000000000000000000000 : ℝ)*base66 + (659488757274999/2500000000000000000000000000 : ℝ)*base68 + (292107971387127/1250000000000000000000000000 : ℝ)*base71 + (361420095299253/2500000000000000000000000000 : ℝ)*base72 + (1386437816832847/5000000000000000000000000000 : ℝ)*base74 + (727462760774999/2500000000000000000000000000 : ℝ)*base76 + (267930444413203/5000000000000000000000000000 : ℝ)*base79 + (10779/25000000000000000 : ℝ)*base86 + (10779/25000000000000000 : ℝ)*base88 + (10779/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4167/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(4167/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8685445461623449605549/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3676359/250000000000 : ℝ)*(base3) + (465212382671/1000000000000 : ℝ)*(base40) + (1300563/125000000000 : ℝ)*(base50) + (475387934119/1000000000000 : ℝ)*(base59) + (2060590060647/1000000000000 : ℝ)*(major_s0_0) + (2060590060647/1000000000000 : ℝ)*(major_s0_1) + (2060590060647/1000000000000 : ℝ)*(major_s0_2) + (26613191/500000000000 : ℝ)*(sp_s0_1) + (2059537/100000000000 : ℝ)*(sp_s0_2) + (1423790629283/500000000000 : ℝ)*(sp_s0_13) + (2847522426489/1000000000000 : ℝ)*(sp_s0_14) + (711890165799/250000000000 : ℝ)*(sp_s0_15) + (1273581841169/1000000000000 : ℝ)*(sp_s0_19) + (2031113/100000000000 : ℝ)*(sp_s0_21) + (318399136651/250000000000 : ℝ)*(f.failure) + (1423790629283/500000000000 : ℝ)*(f.sum) + (492508633/10000000000000000000000 : ℝ)*base62 + (8090895656426473/10000000000000000000000000000 : ℝ)*base64 + (4661498087573527/10000000000000000000000000000 : ℝ)*base66 + (64108541285741/10000000000000000000000000000 : ℝ)*base68 + (4442265951856107/5000000000000000000000000000 : ℝ)*base70 + (354752787573527/10000000000000000000000000000 : ℝ)*base72 + (2591176010714259/10000000000000000000000000000 : ℝ)*base74 + (5972707787285741/10000000000000000000000000000 : ℝ)*base76 + (446479030073527/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (243/25000000000000000 : ℝ)*base87 + (243/25000000000000000 : ℝ)*base89 + (243/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53001/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(53001/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16437448422296048754507/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395566020739/500000000000 : ℝ)*(base40) + (297022198993/1000000000000 : ℝ)*(base50) + (603380901017/1000000000000 : ℝ)*(base59) + (3058981179867/1000000000000 : ℝ)*(major_s0_0) + (1402074251659/200000000000 : ℝ)*(major_s0_1) + (3058981179867/1000000000000 : ℝ)*(major_s0_2) + (35953783/1000000000000 : ℝ)*(sp_s0_0) + (3951390078429/1000000000000 : ℝ)*(sp_s0_4) + (16313909/500000000000 : ℝ)*(sp_s0_14) + (17979/12500000000 : ℝ)*(sp_s0_15) + (4227248363127/1000000000000 : ℝ)*(sp_s0_20) + (1056812922273/250000000000 : ℝ)*(sp_s0_21) + (422728287859/100000000000 : ℝ)*(sp_s0_22) + (47266896279/25000000000 : ℝ)*(sp_s0_25) + (47266896279/25000000000 : ℝ)*(f.failure) + (422728431691/100000000000 : ℝ)*(f.sum) + (934138159403379/2500000000000000000000000000 : ℝ)*base62 + (9559716834918453/10000000000000000000000000000 : ℝ)*base64 + (104064762942981/2000000000000000000000000000 : ℝ)*base67 + (2007826835968599/10000000000000000000000000000 : ℝ)*base69 + (723093087025073/5000000000000000000000000000 : ℝ)*base71 + (1689106224081547/10000000000000000000000000000 : ℝ)*base72 + (151228566116423/2000000000000000000000000000 : ℝ)*base74 + (1586148388031401/10000000000000000000000000000 : ℝ)*base76 + (3906800764183321/5000000000000000000000000000 : ℝ)*base78 + (747/2500000000000000 : ℝ)*base87 + (3247/2500000000000000 : ℝ)*base89 + (747/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (10043/25000 : ℝ) ^ (35/8 : ℝ) ≤ (184997181296443753/10000000000000000000 : ℝ) := by
    have hpowers : (10043/25000 : ℝ)^35 ≤ (184997181296443753/10000000000000000000 : ℝ)^8 := by
      have hnat : (10043 : ℕ)^35*10000000000000000000^8 ≤ 184997181296443753^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10043 25000 184997181296443753 10000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10043/25000 : ℝ)) (X := (184997181296443753/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10184997181296443753/10000000000000000000 : ℝ) ≤ (2510496648687537/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (10184997181296443753/10000000000000000000 : ℝ)^8 ≤ (2510496648687537/2500000000000000 : ℝ)^35 := by
      have hnat : (10184997181296443753 : ℕ)^8*2500000000000000^35 ≤ 2510496648687537^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10184997181296443753 10000000000000000000 2510496648687537 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510496648687537/2500000000000000 : ℝ)) (X := (10184997181296443753/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5184997181296443753/5000000000000000000 : ℝ) ≤ (5041694465982137/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (5184997181296443753/5000000000000000000 : ℝ)^8 ≤ (5041694465982137/5000000000000000 : ℝ)^35 := by
      have hnat : (5184997181296443753 : ℕ)^8*5000000000000000^35 ≤ 5041694465982137^35*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5184997181296443753 5000000000000000000 5041694465982137 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041694465982137/5000000000000000 : ℝ)) (X := (5184997181296443753/5000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10496648687537/1004300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(20701168607063/2008600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (10043/25000 : ℝ)) (alpha := (10496648687537/1004300000000000 : ℝ)) (beta := (20701168607063/2008600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10043/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10496648687537/1004300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(20701168607063/2008600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4167/25000 : ℝ) ^ (35/8 : ℝ) ≤ (39422147320032893/100000000000000000000 : ℝ) := by
    have hpowers : (4167/25000 : ℝ)^35 ≤ (39422147320032893/100000000000000000000 : ℝ)^8 := by
      have hnat : (4167 : ℕ)^35*100000000000000000000^8 ≤ 39422147320032893^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4167 25000 39422147320032893 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4167/25000 : ℝ)) (X := (39422147320032893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100039422147320032893/100000000000000000000 : ℝ) ≤ (5000450470334941/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100039422147320032893/100000000000000000000 : ℝ)^8 ≤ (5000450470334941/5000000000000000 : ℝ)^35 := by
      have hnat : (100039422147320032893 : ℕ)^8*5000000000000000^35 ≤ 5000450470334941^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039422147320032893 100000000000000000000 5000450470334941 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000450470334941/5000000000000000 : ℝ)) (X := (100039422147320032893/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50039422147320032893/50000000000000000000 : ℝ) ≤ (10001801607500941/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50039422147320032893/50000000000000000000 : ℝ)^8 ≤ (10001801607500941/10000000000000000 : ℝ)^35 := by
      have hnat : (50039422147320032893 : ℕ)^8*10000000000000000^35 ≤ 10001801607500941^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039422147320032893 50000000000000000000 10001801607500941 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001801607500941/10000000000000000 : ℝ)) (X := (50039422147320032893/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(450470334941/833400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(900666831059/1666800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (4167/25000 : ℝ)) (alpha := (450470334941/833400000000000 : ℝ)) (beta := (900666831059/1666800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (4167/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(450470334941/833400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(900666831059/1666800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (53001/100000 : ℝ) ^ (35/8 : ℝ) ≤ (6219318224110372091/100000000000000000000 : ℝ) := by
    have hpowers : (53001/100000 : ℝ)^35 ≤ (6219318224110372091/100000000000000000000 : ℝ)^8 := by
      have hnat : (53001 : ℕ)^35*100000000000000000000^8 ≤ 6219318224110372091^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53001 100000 6219318224110372091 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53001/100000 : ℝ)) (X := (6219318224110372091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (106219318224110372091/100000000000000000000 : ℝ) ≤ (2534716443716853/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (106219318224110372091/100000000000000000000 : ℝ)^8 ≤ (2534716443716853/2500000000000000 : ℝ)^35 := by
      have hnat : (106219318224110372091 : ℕ)^8*2500000000000000^35 ≤ 2534716443716853^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106219318224110372091 100000000000000000000 2534716443716853 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2534716443716853/2500000000000000 : ℝ)) (X := (106219318224110372091/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (56219318224110372091/50000000000000000000 : ℝ) ≤ (1283949249105973/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (56219318224110372091/50000000000000000000 : ℝ)^8 ≤ (1283949249105973/1250000000000000 : ℝ)^35 := by
      have hnat : (56219318224110372091 : ℕ)^8*1250000000000000^35 ≤ 1283949249105973^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56219318224110372091 50000000000000000000 1283949249105973 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1283949249105973/1250000000000000 : ℝ)) (X := (56219318224110372091/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(34716443716853/1325025000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(33182054495093/1325025000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (53001/100000 : ℝ)) (alpha := (34716443716853/1325025000000000 : ℝ)) (beta := (33182054495093/1325025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (53001/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(34716443716853/1325025000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(33182054495093/1325025000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-507050889/1250000000 : ℝ)*X 0 0+(168905859/400000000 : ℝ)*X 0 1+(4483028169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5383415177/10000000000 : ℝ)*X 1 0+(-586246297/2500000000 : ℝ)*X 1 1+(969228227/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1512976581/5000000000 : ℝ)*X 2 0+(1239195581/2000000000 : ℝ)*X 2 1+(-1672099581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2892051/6250000 : ℝ)*X 0 0+(3964720993/10000000000 : ℝ)*X 0 1+(2082735491/5000000000 : ℝ)*X 0 2+(2892051/6250000 : ℝ)*X 1 0+(3964720993/10000000000 : ℝ)*X 1 1+(2082735491/5000000000 : ℝ)*X 1 2+(2892051/6250000 : ℝ)*X 2 0+(3964720993/10000000000 : ℝ)*X 2 1+(2082735491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310029_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-304584101140402263389289005220197/45638856835000000000000000000000 : ℝ) := by norm_num
    linear_combination (3427/1000000000000 : ℝ)*(base8) + (4187/1000000000000 : ℝ)*(base13) + (4953/1000000000000 : ℝ)*(base15) + (27997388597/200000000000 : ℝ)*(base40) + (138105262773/500000000000 : ℝ)*(base49) + (481174883111/1000000000000 : ℝ)*(base50) + (241572363473/1000000000000 : ℝ)*(base59) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (2224596326507/1000000000000 : ℝ)*(sp_s1_0) + (139037270573/62500000000 : ℝ)*(sp_s1_1) + (556149083817/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1112298167061/500000000000 : ℝ)*(f.sum) + (116426142222361/3408258750000000000000000000 : ℝ)*base63 + (1143592037057/2355600000000000000000000 : ℝ)*base64 + (1563410808771/4630000000000000000000000 : ℝ)*base67 + (1688000916731/3680625000000000000000000 : ℝ)*base69 + (392119042765447/2310282304687500000000000000 : ℝ)*base70 + (242802721303/1255375000000000000000000 : ℝ)*base72 + (252960167049/578750000000000000000000 : ℝ)*base75 + (5755747610265111/5021500000000000000000000 : ℝ)*base76 + (693569457447857/5812386250000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (573/500000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b017 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=29 := by omega
  rcases hc with rfl
  · exact collision_c310029 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b017 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
