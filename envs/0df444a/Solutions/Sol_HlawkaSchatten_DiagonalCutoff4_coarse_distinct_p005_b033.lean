-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:28:24.310715+00:00
-- url     : https://prove2.me/submissions/b5f6d27a-5273-45de-9c4c-7796710cbe00

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
theorem collision_support_c305077_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2782531139/5000000000 : ℝ)*x 0 + (934454397/2500000000 : ℝ)*x 1 + (3612430851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2782531139/5000000000 : ℝ)^67 ≤ (23151945593981/50000000000000 : ℝ)^51 := by
    have hnat : (2782531139 : ℕ)^67*50000000000000^51 ≤ 23151945593981^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782531139 5000000000 23151945593981 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934454397/2500000000 : ℝ)^67 ≤ (6862423511477/25000000000000 : ℝ)^51 := by
    have hnat : (934454397 : ℕ)^67*25000000000000^51 ≤ 6862423511477^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934454397 2500000000 6862423511477 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3612430851/10000000000 : ℝ)^67 ≤ (13123207374907/50000000000000 : ℝ)^51 := by
    have hnat : (3612430851 : ℕ)^67*50000000000000^51 ≤ 13123207374907^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3612430851 10000000000 13123207374907 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2782531139/5000000000 : ℝ), (934454397/2500000000 : ℝ), (3612430851/10000000000 : ℝ)] ![(23151945593981/50000000000000 : ℝ), (6862423511477/25000000000000 : ℝ), (13123207374907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2782531139/5000000000 : ℝ)|^67 ≤ (23151945593981/50000000000000 : ℝ)^51
        have hw : |(-2782531139/5000000000 : ℝ)|=(2782531139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(934454397/2500000000 : ℝ)|^67 ≤ (6862423511477/25000000000000 : ℝ)^51
        have hw : |(934454397/2500000000 : ℝ)|=(934454397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3612430851/10000000000 : ℝ)|^67 ≤ (13123207374907/50000000000000 : ℝ)^51
        have hw : |(3612430851/10000000000 : ℝ)|=(3612430851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2245960339/5000000000 : ℝ)*x 0 + (5468048991/10000000000 : ℝ)*x 1 + (-2277989/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245960339/5000000000 : ℝ)^67 ≤ (34945492215371/100000000000000 : ℝ)^51 := by
    have hnat : (2245960339 : ℕ)^67*100000000000000^51 ≤ 34945492215371^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245960339 5000000000 34945492215371 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468048991/10000000000 : ℝ)^67 ≤ (45246369436893/100000000000000 : ℝ)^51 := by
    have hnat : (5468048991 : ℕ)^67*100000000000000^51 ≤ 45246369436893^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468048991 10000000000 45246369436893 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277989/7812500 : ℝ)^67 ≤ (19808138338419/100000000000000 : ℝ)^51 := by
    have hnat : (2277989 : ℕ)^67*100000000000000^51 ≤ 19808138338419^51*7812500^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277989 7812500 19808138338419 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245960339/5000000000 : ℝ), (5468048991/10000000000 : ℝ), (-2277989/7812500 : ℝ)] ![(34945492215371/100000000000000 : ℝ), (45246369436893/100000000000000 : ℝ), (19808138338419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245960339/5000000000 : ℝ)|^67 ≤ (34945492215371/100000000000000 : ℝ)^51
        have hw : |(2245960339/5000000000 : ℝ)|=(2245960339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468048991/10000000000 : ℝ)|^67 ≤ (45246369436893/100000000000000 : ℝ)^51
        have hw : |(5468048991/10000000000 : ℝ)|=(5468048991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2277989/7812500 : ℝ)|^67 ≤ (19808138338419/100000000000000 : ℝ)^51
        have hw : |(-2277989/7812500 : ℝ)|=(2277989/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (16868821/80000000 : ℝ)*x 0 + (425613661/625000000 : ℝ)*x 1 + (3659383371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16868821/80000000 : ℝ)^67 ≤ (12939415599973/100000000000000 : ℝ)^51 := by
    have hnat : (16868821 : ℕ)^67*100000000000000^51 ≤ 12939415599973^51*80000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16868821 80000000 12939415599973 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425613661/625000000 : ℝ)^67 ≤ (60365097697557/100000000000000 : ℝ)^51 := by
    have hnat : (425613661 : ℕ)^67*100000000000000^51 ≤ 60365097697557^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425613661 625000000 60365097697557 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3659383371/10000000000 : ℝ)^67 ≤ (26695486682401/100000000000000 : ℝ)^51 := by
    have hnat : (3659383371 : ℕ)^67*100000000000000^51 ≤ 26695486682401^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659383371 10000000000 26695486682401 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16868821/80000000 : ℝ), (425613661/625000000 : ℝ), (3659383371/10000000000 : ℝ)] ![(12939415599973/100000000000000 : ℝ), (60365097697557/100000000000000 : ℝ), (26695486682401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16868821/80000000 : ℝ)|^67 ≤ (12939415599973/100000000000000 : ℝ)^51
        have hw : |(16868821/80000000 : ℝ)|=(16868821/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425613661/625000000 : ℝ)|^67 ≤ (60365097697557/100000000000000 : ℝ)^51
        have hw : |(425613661/625000000 : ℝ)|=(425613661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3659383371/10000000000 : ℝ)|^67 ≤ (26695486682401/100000000000000 : ℝ)^51
        have hw : |(3659383371/10000000000 : ℝ)|=(3659383371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-176040259/312500000 : ℝ)*x 0 + (224763993/625000000 : ℝ)*x 1 + (229764559/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176040259/312500000 : ℝ)^67 ≤ (47051086468319/100000000000000 : ℝ)^51 := by
    have hnat : (176040259 : ℕ)^67*100000000000000^51 ≤ 47051086468319^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176040259 312500000 47051086468319 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224763993/625000000 : ℝ)^67 ≤ (13045914287171/50000000000000 : ℝ)^51 := by
    have hnat : (224763993 : ℕ)^67*50000000000000^51 ≤ 13045914287171^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224763993 625000000 13045914287171 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229764559/625000000 : ℝ)^67 ≤ (26857084947801/100000000000000 : ℝ)^51 := by
    have hnat : (229764559 : ℕ)^67*100000000000000^51 ≤ 26857084947801^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229764559 625000000 26857084947801 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176040259/312500000 : ℝ), (224763993/625000000 : ℝ), (229764559/625000000 : ℝ)] ![(47051086468319/100000000000000 : ℝ), (13045914287171/50000000000000 : ℝ), (26857084947801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176040259/312500000 : ℝ)|^67 ≤ (47051086468319/100000000000000 : ℝ)^51
        have hw : |(-176040259/312500000 : ℝ)|=(176040259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224763993/625000000 : ℝ)|^67 ≤ (13045914287171/50000000000000 : ℝ)^51
        have hw : |(224763993/625000000 : ℝ)|=(224763993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229764559/625000000 : ℝ)|^67 ≤ (26857084947801/100000000000000 : ℝ)^51
        have hw : |(229764559/625000000 : ℝ)|=(229764559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1889572581/5000000000 : ℝ)*x 0 + (-547126329/2500000000 : ℝ)*x 1 + (6654559337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1889572581/5000000000 : ℝ)^67 ≤ (13924550041659/50000000000000 : ℝ)^51 := by
    have hnat : (1889572581 : ℕ)^67*50000000000000^51 ≤ 13924550041659^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889572581 5000000000 13924550041659 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547126329/2500000000 : ℝ)^67 ≤ (13587360243781/100000000000000 : ℝ)^51 := by
    have hnat : (547126329 : ℕ)^67*100000000000000^51 ≤ 13587360243781^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547126329 2500000000 13587360243781 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6654559337/10000000000 : ℝ)^67 ≤ (7320442457489/12500000000000 : ℝ)^51 := by
    have hnat : (6654559337 : ℕ)^67*12500000000000^51 ≤ 7320442457489^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6654559337 10000000000 7320442457489 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1889572581/5000000000 : ℝ), (-547126329/2500000000 : ℝ), (6654559337/10000000000 : ℝ)] ![(13924550041659/50000000000000 : ℝ), (13587360243781/100000000000000 : ℝ), (7320442457489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1889572581/5000000000 : ℝ)|^67 ≤ (13924550041659/50000000000000 : ℝ)^51
        have hw : |(1889572581/5000000000 : ℝ)|=(1889572581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547126329/2500000000 : ℝ)|^67 ≤ (13587360243781/100000000000000 : ℝ)^51
        have hw : |(-547126329/2500000000 : ℝ)|=(547126329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6654559337/10000000000 : ℝ)|^67 ≤ (7320442457489/12500000000000 : ℝ)^51
        have hw : |(6654559337/10000000000 : ℝ)|=(6654559337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1093041239/2500000000 : ℝ)*x 0 + (2815312377/5000000000 : ℝ)*x 1 + (-2853235273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093041239/2500000000 : ℝ)^67 ≤ (6745340542237/20000000000000 : ℝ)^51 := by
    have hnat : (1093041239 : ℕ)^67*20000000000000^51 ≤ 6745340542237^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093041239 2500000000 6745340542237 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2815312377/5000000000 : ℝ)^67 ≤ (47021862557409/100000000000000 : ℝ)^51 := by
    have hnat : (2815312377 : ℕ)^67*100000000000000^51 ≤ 47021862557409^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815312377 5000000000 47021862557409 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2853235273/10000000000 : ℝ)^67 ≤ (154011477753/800000000000 : ℝ)^51 := by
    have hnat : (2853235273 : ℕ)^67*800000000000^51 ≤ 154011477753^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853235273 10000000000 154011477753 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093041239/2500000000 : ℝ), (2815312377/5000000000 : ℝ), (-2853235273/10000000000 : ℝ)] ![(6745340542237/20000000000000 : ℝ), (47021862557409/100000000000000 : ℝ), (154011477753/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093041239/2500000000 : ℝ)|^67 ≤ (6745340542237/20000000000000 : ℝ)^51
        have hw : |(1093041239/2500000000 : ℝ)|=(1093041239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2815312377/5000000000 : ℝ)|^67 ≤ (47021862557409/100000000000000 : ℝ)^51
        have hw : |(2815312377/5000000000 : ℝ)|=(2815312377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2853235273/10000000000 : ℝ)|^67 ≤ (154011477753/800000000000 : ℝ)^51
        have hw : |(-2853235273/10000000000 : ℝ)|=(2853235273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_12 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1956703689/10000000000 : ℝ)*x 0 + (7086408917/10000000000 : ℝ)*x 1 + (861372099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1956703689/10000000000 : ℝ)^67 ≤ (5864465307577/50000000000000 : ℝ)^51 := by
    have hnat : (1956703689 : ℕ)^67*50000000000000^51 ≤ 5864465307577^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956703689 10000000000 5864465307577 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7086408917/10000000000 : ℝ)^67 ≤ (63606441391769/100000000000000 : ℝ)^51 := by
    have hnat : (7086408917 : ℕ)^67*100000000000000^51 ≤ 63606441391769^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7086408917 10000000000 63606441391769 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861372099/2500000000 : ℝ)^67 ≤ (24664627981911/100000000000000 : ℝ)^51 := by
    have hnat : (861372099 : ℕ)^67*100000000000000^51 ≤ 24664627981911^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861372099 2500000000 24664627981911 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1956703689/10000000000 : ℝ), (7086408917/10000000000 : ℝ), (861372099/2500000000 : ℝ)] ![(5864465307577/50000000000000 : ℝ), (63606441391769/100000000000000 : ℝ), (24664627981911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1956703689/10000000000 : ℝ)|^67 ≤ (5864465307577/50000000000000 : ℝ)^51
        have hw : |(1956703689/10000000000 : ℝ)|=(1956703689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7086408917/10000000000 : ℝ)|^67 ≤ (63606441391769/100000000000000 : ℝ)^51
        have hw : |(7086408917/10000000000 : ℝ)|=(7086408917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(861372099/2500000000 : ℝ)|^67 ≤ (24664627981911/100000000000000 : ℝ)^51
        have hw : |(861372099/2500000000 : ℝ)|=(861372099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5590843297/10000000000 : ℝ)*x 0 + (3744244807/10000000000 : ℝ)*x 1 + (3576330429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5590843297/10000000000 : ℝ)^67 ≤ (46585903010553/100000000000000 : ℝ)^51 := by
    have hnat : (5590843297 : ℕ)^67*100000000000000^51 ≤ 46585903010553^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590843297 10000000000 46585903010553 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3744244807/10000000000 : ℝ)^67 ≤ (6877929669933/25000000000000 : ℝ)^51 := by
    have hnat : (3744244807 : ℕ)^67*25000000000000^51 ≤ 6877929669933^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744244807 10000000000 6877929669933 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3576330429/10000000000 : ℝ)^67 ≤ (6475594575549/25000000000000 : ℝ)^51 := by
    have hnat : (3576330429 : ℕ)^67*25000000000000^51 ≤ 6475594575549^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576330429 10000000000 6475594575549 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5590843297/10000000000 : ℝ), (3744244807/10000000000 : ℝ), (3576330429/10000000000 : ℝ)] ![(46585903010553/100000000000000 : ℝ), (6877929669933/25000000000000 : ℝ), (6475594575549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5590843297/10000000000 : ℝ)|^67 ≤ (46585903010553/100000000000000 : ℝ)^51
        have hw : |(-5590843297/10000000000 : ℝ)|=(5590843297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3744244807/10000000000 : ℝ)|^67 ≤ (6877929669933/25000000000000 : ℝ)^51
        have hw : |(3744244807/10000000000 : ℝ)|=(3744244807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3576330429/10000000000 : ℝ)|^67 ≤ (6475594575549/25000000000000 : ℝ)^51
        have hw : |(3576330429/10000000000 : ℝ)|=(3576330429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (188208273/500000000 : ℝ)*x 0 + (-466563361/2000000000 : ℝ)*x 1 + (6564055933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188208273/500000000 : ℝ)^67 ≤ (27704171171361/100000000000000 : ℝ)^51 := by
    have hnat : (188208273 : ℕ)^67*100000000000000^51 ≤ 27704171171361^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188208273 500000000 27704171171361 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466563361/2000000000 : ℝ)^67 ≤ (14776401312617/100000000000000 : ℝ)^51 := by
    have hnat : (466563361 : ℕ)^67*100000000000000^51 ≤ 14776401312617^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466563361 2000000000 14776401312617 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6564055933/10000000000 : ℝ)^67 ≤ (28759713751099/50000000000000 : ℝ)^51 := by
    have hnat : (6564055933 : ℕ)^67*50000000000000^51 ≤ 28759713751099^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6564055933 10000000000 28759713751099 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(188208273/500000000 : ℝ), (-466563361/2000000000 : ℝ), (6564055933/10000000000 : ℝ)] ![(27704171171361/100000000000000 : ℝ), (14776401312617/100000000000000 : ℝ), (28759713751099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(188208273/500000000 : ℝ)|^67 ≤ (27704171171361/100000000000000 : ℝ)^51
        have hw : |(188208273/500000000 : ℝ)|=(188208273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466563361/2000000000 : ℝ)|^67 ≤ (14776401312617/100000000000000 : ℝ)^51
        have hw : |(-466563361/2000000000 : ℝ)|=(466563361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6564055933/10000000000 : ℝ)|^67 ≤ (28759713751099/50000000000000 : ℝ)^51
        have hw : |(6564055933/10000000000 : ℝ)|=(6564055933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4460279329/10000000000 : ℝ)*x 0 + (683383867/1250000000 : ℝ)*x 1 + (-11812551/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460279329/10000000000 : ℝ)^67 ≤ (6924493197571/20000000000000 : ℝ)^51 := by
    have hnat : (4460279329 : ℕ)^67*20000000000000^51 ≤ 6924493197571^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460279329 10000000000 6924493197571 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683383867/1250000000 : ℝ)^67 ≤ (45235737630523/100000000000000 : ℝ)^51 := by
    have hnat : (683383867 : ℕ)^67*100000000000000^51 ≤ 45235737630523^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683383867 1250000000 45235737630523 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11812551/40000000 : ℝ)^67 ≤ (5035449092279/25000000000000 : ℝ)^51 := by
    have hnat : (11812551 : ℕ)^67*25000000000000^51 ≤ 5035449092279^51*40000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11812551 40000000 5035449092279 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460279329/10000000000 : ℝ), (683383867/1250000000 : ℝ), (-11812551/40000000 : ℝ)] ![(6924493197571/20000000000000 : ℝ), (45235737630523/100000000000000 : ℝ), (5035449092279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460279329/10000000000 : ℝ)|^67 ≤ (6924493197571/20000000000000 : ℝ)^51
        have hw : |(4460279329/10000000000 : ℝ)|=(4460279329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683383867/1250000000 : ℝ)|^67 ≤ (45235737630523/100000000000000 : ℝ)^51
        have hw : |(683383867/1250000000 : ℝ)|=(683383867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11812551/40000000 : ℝ)|^67 ≤ (5035449092279/25000000000000 : ℝ)^51
        have hw : |(-11812551/40000000 : ℝ)|=(11812551/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_17 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (4999999999/5000000000 : ℝ)*x 1 + (-419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^67 ≤ (0 : ℝ)^51 := by
    have hnat : (0 : ℕ)^67*1^51 ≤ 0^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999999999/5000000000 : ℝ)^67 ≤ (49999999986863/50000000000000 : ℝ)^51 := by
    have hnat : (4999999999 : ℕ)^67*50000000000000^51 ≤ 49999999986863^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999999 5000000000 49999999986863 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419/10000000000 : ℝ)^67 ≤ (10153/50000000000000 : ℝ)^51 := by
    have hnat : (419 : ℕ)^67*50000000000000^51 ≤ 10153^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419 10000000000 10153 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (4999999999/5000000000 : ℝ), (-419/10000000000 : ℝ)] ![(0 : ℝ), (49999999986863/50000000000000 : ℝ), (10153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^67 ≤ (0 : ℝ)^51
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4999999999/5000000000 : ℝ)|^67 ≤ (49999999986863/50000000000000 : ℝ)^51
        have hw : |(4999999999/5000000000 : ℝ)|=(4999999999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419/10000000000 : ℝ)|^67 ≤ (10153/50000000000000 : ℝ)^51
        have hw : |(-419/10000000000 : ℝ)|=(419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_19 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2146000477/10000000000 : ℝ)*x 0 + (6806534813/10000000000 : ℝ)*x 1 + (3631794997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146000477/10000000000 : ℝ)^67 ≤ (13241739806989/100000000000000 : ℝ)^51 := by
    have hnat : (2146000477 : ℕ)^67*100000000000000^51 ≤ 13241739806989^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146000477 10000000000 13241739806989 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6806534813/10000000000 : ℝ)^67 ≤ (60326859805531/100000000000000 : ℝ)^51 := by
    have hnat : (6806534813 : ℕ)^67*100000000000000^51 ≤ 60326859805531^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6806534813 10000000000 60326859805531 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3631794997/10000000000 : ℝ)^67 ≤ (660785009533/2500000000000 : ℝ)^51 := by
    have hnat : (3631794997 : ℕ)^67*2500000000000^51 ≤ 660785009533^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3631794997 10000000000 660785009533 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146000477/10000000000 : ℝ), (6806534813/10000000000 : ℝ), (3631794997/10000000000 : ℝ)] ![(13241739806989/100000000000000 : ℝ), (60326859805531/100000000000000 : ℝ), (660785009533/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146000477/10000000000 : ℝ)|^67 ≤ (13241739806989/100000000000000 : ℝ)^51
        have hw : |(2146000477/10000000000 : ℝ)|=(2146000477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6806534813/10000000000 : ℝ)|^67 ≤ (60326859805531/100000000000000 : ℝ)^51
        have hw : |(6806534813/10000000000 : ℝ)|=(6806534813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3631794997/10000000000 : ℝ)|^67 ≤ (660785009533/2500000000000 : ℝ)^51
        have hw : |(3631794997/10000000000 : ℝ)|=(3631794997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5578934673/10000000000 : ℝ)*x 0 + (757958591/2000000000 : ℝ)*x 1 + (1771841523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5578934673/10000000000 : ℝ)^67 ≤ (9291117374199/20000000000000 : ℝ)^51 := by
    have hnat : (5578934673 : ℕ)^67*20000000000000^51 ≤ 9291117374199^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5578934673 10000000000 9291117374199 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757958591/2000000000 : ℝ)^67 ≤ (6988056842663/25000000000000 : ℝ)^51 := by
    have hnat : (757958591 : ℕ)^67*25000000000000^51 ≤ 6988056842663^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757958591 2000000000 6988056842663 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1771841523/5000000000 : ℝ)^67 ≤ (12796092876567/50000000000000 : ℝ)^51 := by
    have hnat : (1771841523 : ℕ)^67*50000000000000^51 ≤ 12796092876567^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771841523 5000000000 12796092876567 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5578934673/10000000000 : ℝ), (757958591/2000000000 : ℝ), (1771841523/5000000000 : ℝ)] ![(9291117374199/20000000000000 : ℝ), (6988056842663/25000000000000 : ℝ), (12796092876567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5578934673/10000000000 : ℝ)|^67 ≤ (9291117374199/20000000000000 : ℝ)^51
        have hw : |(-5578934673/10000000000 : ℝ)|=(5578934673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(757958591/2000000000 : ℝ)|^67 ≤ (6988056842663/25000000000000 : ℝ)^51
        have hw : |(757958591/2000000000 : ℝ)|=(757958591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1771841523/5000000000 : ℝ)|^67 ≤ (12796092876567/50000000000000 : ℝ)^51
        have hw : |(1771841523/5000000000 : ℝ)|=(1771841523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3713767907/10000000000 : ℝ)*x 0 + (-572714281/2500000000 : ℝ)*x 1 + (6636415951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3713767907/10000000000 : ℝ)^67 ≤ (6804476083097/25000000000000 : ℝ)^51 := by
    have hnat : (3713767907 : ℕ)^67*25000000000000^51 ≤ 6804476083097^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713767907 10000000000 6804476083097 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572714281/2500000000 : ℝ)^67 ≤ (14428230242093/100000000000000 : ℝ)^51 := by
    have hnat : (572714281 : ℕ)^67*100000000000000^51 ≤ 14428230242093^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572714281 2500000000 14428230242093 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6636415951/10000000000 : ℝ)^67 ≤ (5835386541467/10000000000000 : ℝ)^51 := by
    have hnat : (6636415951 : ℕ)^67*10000000000000^51 ≤ 5835386541467^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6636415951 10000000000 5835386541467 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3713767907/10000000000 : ℝ), (-572714281/2500000000 : ℝ), (6636415951/10000000000 : ℝ)] ![(6804476083097/25000000000000 : ℝ), (14428230242093/100000000000000 : ℝ), (5835386541467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3713767907/10000000000 : ℝ)|^67 ≤ (6804476083097/25000000000000 : ℝ)^51
        have hw : |(3713767907/10000000000 : ℝ)|=(3713767907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572714281/2500000000 : ℝ)|^67 ≤ (14428230242093/100000000000000 : ℝ)^51
        have hw : |(-572714281/2500000000 : ℝ)|=(572714281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6636415951/10000000000 : ℝ)|^67 ≤ (5835386541467/10000000000000 : ℝ)^51
        have hw : |(6636415951/10000000000 : ℝ)|=(6636415951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4639870721/10000000000 : ℝ)*x 0 + (1060327401/2000000000 : ℝ)*x 1 + (-2947199093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4639870721/10000000000 : ℝ)^67 ≤ (4558167569897/12500000000000 : ℝ)^51 := by
    have hnat : (4639870721 : ℕ)^67*12500000000000^51 ≤ 4558167569897^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639870721 10000000000 4558167569897 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060327401/2000000000 : ℝ)^67 ≤ (5430757249707/12500000000000 : ℝ)^51 := by
    have hnat : (1060327401 : ℕ)^67*12500000000000^51 ≤ 5430757249707^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060327401 2000000000 5430757249707 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2947199093/10000000000 : ℝ)^67 ≤ (20088601433963/100000000000000 : ℝ)^51 := by
    have hnat : (2947199093 : ℕ)^67*100000000000000^51 ≤ 20088601433963^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947199093 10000000000 20088601433963 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4639870721/10000000000 : ℝ), (1060327401/2000000000 : ℝ), (-2947199093/10000000000 : ℝ)] ![(4558167569897/12500000000000 : ℝ), (5430757249707/12500000000000 : ℝ), (20088601433963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4639870721/10000000000 : ℝ)|^67 ≤ (4558167569897/12500000000000 : ℝ)^51
        have hw : |(4639870721/10000000000 : ℝ)|=(4639870721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060327401/2000000000 : ℝ)|^67 ≤ (5430757249707/12500000000000 : ℝ)^51
        have hw : |(1060327401/2000000000 : ℝ)|=(1060327401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2947199093/10000000000 : ℝ)|^67 ≤ (20088601433963/100000000000000 : ℝ)^51
        have hw : |(-2947199093/10000000000 : ℝ)|=(2947199093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s0_25 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1904561451/10000000000 : ℝ)*x 0 + (3577239439/5000000000 : ℝ)*x 1 + (1701703271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1904561451/10000000000 : ℝ)^67 ≤ (11320049344057/100000000000000 : ℝ)^51 := by
    have hnat : (1904561451 : ℕ)^67*100000000000000^51 ≤ 11320049344057^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904561451 10000000000 11320049344057 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3577239439/5000000000 : ℝ)^67 ≤ (64410314462373/100000000000000 : ℝ)^51 := by
    have hnat : (3577239439 : ℕ)^67*100000000000000^51 ≤ 64410314462373^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577239439 5000000000 64410314462373 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1701703271/5000000000 : ℝ)^67 ≤ (12134818089647/50000000000000 : ℝ)^51 := by
    have hnat : (1701703271 : ℕ)^67*50000000000000^51 ≤ 12134818089647^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701703271 5000000000 12134818089647 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1904561451/10000000000 : ℝ), (3577239439/5000000000 : ℝ), (1701703271/5000000000 : ℝ)] ![(11320049344057/100000000000000 : ℝ), (64410314462373/100000000000000 : ℝ), (12134818089647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1904561451/10000000000 : ℝ)|^67 ≤ (11320049344057/100000000000000 : ℝ)^51
        have hw : |(1904561451/10000000000 : ℝ)|=(1904561451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3577239439/5000000000 : ℝ)|^67 ≤ (64410314462373/100000000000000 : ℝ)^51
        have hw : |(3577239439/5000000000 : ℝ)|=(3577239439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1701703271/5000000000 : ℝ)|^67 ≤ (12134818089647/50000000000000 : ℝ)^51
        have hw : |(1701703271/5000000000 : ℝ)|=(1701703271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-305037023/625000000 : ℝ)*x 0 + (4051446633/10000000000 : ℝ)*x 1 + (50643231/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (305037023/625000000 : ℝ)^67 ≤ (38970720055041/100000000000000 : ℝ)^51 := by
    have hnat : (305037023 : ℕ)^67*100000000000000^51 ≤ 38970720055041^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305037023 625000000 38970720055041 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051446633/10000000000 : ℝ)^67 ≤ (30514581351487/100000000000000 : ℝ)^51 := by
    have hnat : (4051446633 : ℕ)^67*100000000000000^51 ≤ 30514581351487^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051446633 10000000000 30514581351487 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50643231/125000000 : ℝ)^67 ≤ (1525734928693/5000000000000 : ℝ)^51 := by
    have hnat : (50643231 : ℕ)^67*5000000000000^51 ≤ 1525734928693^51*125000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50643231 125000000 1525734928693 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-305037023/625000000 : ℝ), (4051446633/10000000000 : ℝ), (50643231/125000000 : ℝ)] ![(38970720055041/100000000000000 : ℝ), (30514581351487/100000000000000 : ℝ), (1525734928693/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-305037023/625000000 : ℝ)|^67 ≤ (38970720055041/100000000000000 : ℝ)^51
        have hw : |(-305037023/625000000 : ℝ)|=(305037023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4051446633/10000000000 : ℝ)|^67 ≤ (30514581351487/100000000000000 : ℝ)^51
        have hw : |(4051446633/10000000000 : ℝ)|=(4051446633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50643231/125000000 : ℝ)|^67 ≤ (1525734928693/5000000000000 : ℝ)^51
        have hw : |(50643231/125000000 : ℝ)|=(50643231/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4193115851/10000000000 : ℝ)*x 0 + (-435095369/1250000000 : ℝ)*x 1 + (329219949/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193115851/10000000000 : ℝ)^67 ≤ (31923981724297/100000000000000 : ℝ)^51 := by
    have hnat : (4193115851 : ℕ)^67*100000000000000^51 ≤ 31923981724297^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193115851 10000000000 31923981724297 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435095369/1250000000 : ℝ)^67 ≤ (24996893466863/100000000000000 : ℝ)^51 := by
    have hnat : (435095369 : ℕ)^67*100000000000000^51 ≤ 24996893466863^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435095369 1250000000 24996893466863 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329219949/625000000 : ℝ)^67 ≤ (4307912478151/10000000000000 : ℝ)^51 := by
    have hnat : (329219949 : ℕ)^67*10000000000000^51 ≤ 4307912478151^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329219949 625000000 4307912478151 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193115851/10000000000 : ℝ), (-435095369/1250000000 : ℝ), (329219949/625000000 : ℝ)] ![(31923981724297/100000000000000 : ℝ), (24996893466863/100000000000000 : ℝ), (4307912478151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193115851/10000000000 : ℝ)|^67 ≤ (31923981724297/100000000000000 : ℝ)^51
        have hw : |(4193115851/10000000000 : ℝ)|=(4193115851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435095369/1250000000 : ℝ)|^67 ≤ (24996893466863/100000000000000 : ℝ)^51
        have hw : |(-435095369/1250000000 : ℝ)|=(435095369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329219949/625000000 : ℝ)|^67 ≤ (4307912478151/10000000000000 : ℝ)^51
        have hw : |(329219949/625000000 : ℝ)|=(329219949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2096553397/5000000000 : ℝ)*x 0 + (32922033/62500000 : ℝ)*x 1 + (-870191403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096553397/5000000000 : ℝ)^67 ≤ (31923891136637/100000000000000 : ℝ)^51 := by
    have hnat : (2096553397 : ℕ)^67*100000000000000^51 ≤ 31923891136637^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096553397 5000000000 31923891136637 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32922033/62500000 : ℝ)^67 ≤ (43079190276851/100000000000000 : ℝ)^51 := by
    have hnat : (32922033 : ℕ)^67*100000000000000^51 ≤ 43079190276851^51*62500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32922033 62500000 43079190276851 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870191403/2500000000 : ℝ)^67 ≤ (24996918562481/100000000000000 : ℝ)^51 := by
    have hnat : (870191403 : ℕ)^67*100000000000000^51 ≤ 24996918562481^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870191403 2500000000 24996918562481 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096553397/5000000000 : ℝ), (32922033/62500000 : ℝ), (-870191403/2500000000 : ℝ)] ![(31923891136637/100000000000000 : ℝ), (43079190276851/100000000000000 : ℝ), (24996918562481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096553397/5000000000 : ℝ)|^67 ≤ (31923891136637/100000000000000 : ℝ)^51
        have hw : |(2096553397/5000000000 : ℝ)|=(2096553397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32922033/62500000 : ℝ)|^67 ≤ (43079190276851/100000000000000 : ℝ)^51
        have hw : |(32922033/62500000 : ℝ)|=(32922033/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-870191403/2500000000 : ℝ)|^67 ≤ (24996918562481/100000000000000 : ℝ)^51
        have hw : |(-870191403/2500000000 : ℝ)|=(870191403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305077_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1847395541/5000000000 : ℝ)*x 0 + (4641523907/10000000000 : ℝ)*x 1 + (464150851/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1847395541/5000000000 : ℝ)^67 ≤ (5407067704441/20000000000000 : ℝ)^51 := by
    have hnat : (1847395541 : ℕ)^67*20000000000000^51 ≤ 5407067704441^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847395541 5000000000 5407067704441 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4641523907/10000000000 : ℝ)^67 ≤ (36482410224623/100000000000000 : ℝ)^51 := by
    have hnat : (4641523907 : ℕ)^67*100000000000000^51 ≤ 36482410224623^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4641523907 10000000000 36482410224623 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464150851/1000000000 : ℝ)^67 ≤ (18241125618477/50000000000000 : ℝ)^51 := by
    have hnat : (464150851 : ℕ)^67*50000000000000^51 ≤ 18241125618477^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464150851 1000000000 18241125618477 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1847395541/5000000000 : ℝ), (4641523907/10000000000 : ℝ), (464150851/1000000000 : ℝ)] ![(5407067704441/20000000000000 : ℝ), (36482410224623/100000000000000 : ℝ), (18241125618477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1847395541/5000000000 : ℝ)|^67 ≤ (5407067704441/20000000000000 : ℝ)^51
        have hw : |(1847395541/5000000000 : ℝ)|=(1847395541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4641523907/10000000000 : ℝ)|^67 ≤ (36482410224623/100000000000000 : ℝ)^51
        have hw : |(4641523907/10000000000 : ℝ)|=(4641523907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464150851/1000000000 : ℝ)|^67 ≤ (18241125618477/50000000000000 : ℝ)^51
        have hw : |(464150851/1000000000 : ℝ)|=(464150851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305077 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2782531139/5000000000 : ℝ)*X 0 0+(934454397/2500000000 : ℝ)*X 0 1+(3612430851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2245960339/5000000000 : ℝ)*X 2 0+(5468048991/10000000000 : ℝ)*X 2 1+(-2277989/7812500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((16868821/80000000 : ℝ)*X 0 0+(425613661/625000000 : ℝ)*X 0 1+(3659383371/10000000000 : ℝ)*X 0 2+(16868821/80000000 : ℝ)*X 1 0+(425613661/625000000 : ℝ)*X 1 1+(3659383371/10000000000 : ℝ)*X 1 2+(16868821/80000000 : ℝ)*X 2 0+(425613661/625000000 : ℝ)*X 2 1+(3659383371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-176040259/312500000 : ℝ)*X 0 0+(224763993/625000000 : ℝ)*X 0 1+(229764559/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1889572581/5000000000 : ℝ)*X 1 0+(-547126329/2500000000 : ℝ)*X 1 1+(6654559337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1093041239/2500000000 : ℝ)*X 2 0+(2815312377/5000000000 : ℝ)*X 2 1+(-2853235273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((1956703689/10000000000 : ℝ)*X 0 0+(7086408917/10000000000 : ℝ)*X 0 1+(861372099/2500000000 : ℝ)*X 0 2+(1956703689/10000000000 : ℝ)*X 1 0+(7086408917/10000000000 : ℝ)*X 1 1+(861372099/2500000000 : ℝ)*X 1 2+(1956703689/10000000000 : ℝ)*X 2 0+(7086408917/10000000000 : ℝ)*X 2 1+(861372099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5590843297/10000000000 : ℝ)*X 0 0+(3744244807/10000000000 : ℝ)*X 0 1+(3576330429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((188208273/500000000 : ℝ)*X 1 0+(-466563361/2000000000 : ℝ)*X 1 1+(6564055933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4460279329/10000000000 : ℝ)*X 2 0+(683383867/1250000000 : ℝ)*X 2 1+(-11812551/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((4999999999/5000000000 : ℝ)*X 0 1+(-419/10000000000 : ℝ)*X 0 2+(4999999999/5000000000 : ℝ)*X 2 1+(-419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_17 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((2146000477/10000000000 : ℝ)*X 0 0+(6806534813/10000000000 : ℝ)*X 0 1+(3631794997/10000000000 : ℝ)*X 0 2+(2146000477/10000000000 : ℝ)*X 1 0+(6806534813/10000000000 : ℝ)*X 1 1+(3631794997/10000000000 : ℝ)*X 1 2+(2146000477/10000000000 : ℝ)*X 2 0+(6806534813/10000000000 : ℝ)*X 2 1+(3631794997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5578934673/10000000000 : ℝ)*X 0 0+(757958591/2000000000 : ℝ)*X 0 1+(1771841523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3713767907/10000000000 : ℝ)*X 1 0+(-572714281/2500000000 : ℝ)*X 1 1+(6636415951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4639870721/10000000000 : ℝ)*X 2 0+(1060327401/2000000000 : ℝ)*X 2 1+(-2947199093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1904561451/10000000000 : ℝ)*X 0 0+(3577239439/5000000000 : ℝ)*X 0 1+(1701703271/5000000000 : ℝ)*X 0 2+(1904561451/10000000000 : ℝ)*X 1 0+(3577239439/5000000000 : ℝ)*X 1 1+(1701703271/5000000000 : ℝ)*X 1 2+(1904561451/10000000000 : ℝ)*X 2 0+(3577239439/5000000000 : ℝ)*X 2 1+(1701703271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((20723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1524112558310956808967/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1111818209857/500000000000 : ℝ)*(base49) + (871630799009/200000000000 : ℝ)*(base60) + (502088275431/20000000000 : ℝ)*(major_s0_0) + (19354932532279/500000000000 : ℝ)*(major_s0_1) + (502088275431/20000000000 : ℝ)*(major_s0_2) + (122617851/1000000000000 : ℝ)*(sp_s0_0) + (82074477/1000000000000 : ℝ)*(sp_s0_6) + (16896432311397/500000000000 : ℝ)*(sp_s0_7) + (33792443278801/1000000000000 : ℝ)*(sp_s0_8) + (16896398605951/500000000000 : ℝ)*(sp_s0_9) + (16415756602253/1000000000000 : ℝ)*(sp_s0_12) + (190028743/1000000000000 : ℝ)*(sp_s0_15) + (850340705813/62500000000 : ℝ)*(sp_s0_17) + (135990461/250000000000 : ℝ)*(sp_s0_21) + (1641583867673/100000000000 : ℝ)*(f.failure) + (6758597448129/200000000000 : ℝ)*(f.sum) + (644004873736313/5000000000000000000000000000 : ℝ)*base63 + (91312485580393/200000000000000000000000000 : ℝ)*base65 + (929682098049009/2500000000000000000000000000 : ℝ)*base67 + (37457472006401/100000000000000000000000000 : ℝ)*base69 + (11111511647591/200000000000000000000000000 : ℝ)*base71 + (104706254800393/200000000000000000000000000 : ℝ)*base73 + (3655438412916263/5000000000000000000000000000 : ℝ)*base75 + (50461637943599/100000000000000000000000000 : ℝ)*base77 + (315988949392157/5000000000000000000000000000 : ℝ)*base78 + (27/78125000000000 : ℝ)*base86 + (27/78125000000000 : ℝ)*base88 + (27/78125000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((243/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(243/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4125028706501037562437/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3533887/1000000000000 : ℝ)*(base40) + (1387305521607/1000000000000 : ℝ)*(base49) + (1721459491219/1000000000000 : ℝ)*(base60) + (1003800591439/100000000000 : ℝ)*(major_s0_0) + (1003800591439/100000000000 : ℝ)*(major_s0_1) + (1003800591439/100000000000 : ℝ)*(major_s0_2) + (353333/500000000000 : ℝ)*(sp_s0_2) + (367897821/500000000000 : ℝ)*(sp_s0_7) + (13511393470431/1000000000000 : ℝ)*(sp_s0_13) + (13512128189267/1000000000000 : ℝ)*(sp_s0_14) + (1351187623461/100000000000 : ℝ)*(sp_s0_15) + (820484632833/125000000000 : ℝ)*(sp_s0_19) + (538403/500000000000 : ℝ)*(sp_s0_21) + (63081199/250000000000 : ℝ)*(sp_s0_22) + (820484632833/125000000000 : ℝ)*(f.failure) + (13512129266073/1000000000000 : ℝ)*(f.sum) + (821365838337521/1000000000000000000000000000 : ℝ)*base63 + (201977219462783/1000000000000000000000000000 : ℝ)*base64 + (209103109812631/500000000000000000000000000 : ℝ)*base66 + (20291558437369/500000000000000000000000000 : ℝ)*base69 + (307648116137521/1000000000000000000000000000 : ℝ)*base70 + (117824807462783/1000000000000000000000000000 : ℝ)*base72 + (349394756762783/1000000000000000000000000000 : ℝ)*base75 + (283273576837369/500000000000000000000000000 : ℝ)*base76 + (19839610982391/200000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1253/1562500000000000 : ℝ)*base87 + (1253/1562500000000000 : ℝ)*base89 + (1253/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(10191/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(10191/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (76409361206970710305929/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1058092427447/1000000000000 : ℝ)*(base49) + (561481899199/200000000000 : ℝ)*(base60) + (392385521259/20000000000 : ℝ)*(major_s0_0) + (31916786194737/1000000000000 : ℝ)*(major_s0_1) + (392385521259/20000000000 : ℝ)*(major_s0_2) + (926823143/1000000000000 : ℝ)*(sp_s0_2) + (164104569/500000000000 : ℝ)*(sp_s0_8) + (197343917/100000000000 : ℝ)*(sp_s0_12) + (355451377/200000000000 : ℝ)*(sp_s0_14) + (12297510131787/1000000000000 : ℝ)*(sp_s0_17) + (13204726780591/500000000000 : ℝ)*(sp_s0_20) + (13203674047579/500000000000 : ℝ)*(sp_s0_21) + (13204263369019/500000000000 : ℝ)*(sp_s0_22) + (6413560015791/500000000000 : ℝ)*(sp_s0_25) + (12829093470751/1000000000000 : ℝ)*(f.failure) + (13204726780591/500000000000 : ℝ)*(f.sum) + (4939334104176011/10000000000000000000000000000 : ℝ)*base62 + (299243351411323/200000000000000000000000000 : ℝ)*base64 + (3606242160182073/5000000000000000000000000000 : ℝ)*base66 + (58062212209411/100000000000000000000000000 : ℝ)*base68 + (227872437252501/200000000000000000000000000 : ℝ)*base70 + (66513413631323/200000000000000000000000000 : ℝ)*base72 + (6123033095234911/10000000000000000000000000000 : ℝ)*base74 + (72084343680589/100000000000000000000000000 : ℝ)*base76 + (499781537866287/1250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (279/3125000000000000 : ℝ)*base87 + (279/3125000000000000 : ℝ)*base89 + (279/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (20723/100000 : ℝ) ^ (133/32 : ℝ) ≤ (144213604214029339/100000000000000000000 : ℝ) := by
    have hpowers : (20723/100000 : ℝ)^133 ≤ (144213604214029339/100000000000000000000 : ℝ)^32 := by
      have hnat : (20723 : ℕ)^133*100000000000000000000^32 ≤ 144213604214029339^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20723 100000 144213604214029339 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20723/100000 : ℝ)) (X := (144213604214029339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100144213604214029339/100000000000000000000 : ℝ) ≤ (10003467902622397/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (100144213604214029339/100000000000000000000 : ℝ)^32 ≤ (10003467902622397/10000000000000000 : ℝ)^133 := by
      have hnat : (100144213604214029339 : ℕ)^32*10000000000000000^133 ≤ 10003467902622397^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100144213604214029339 100000000000000000000 10003467902622397 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003467902622397/10000000000000000 : ℝ)) (X := (100144213604214029339/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50144213604214029339/50000000000000000000 : ℝ) ≤ (10006932014890919/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50144213604214029339/50000000000000000000 : ℝ)^32 ≤ (10006932014890919/10000000000000000 : ℝ)^133 := by
      have hnat : (50144213604214029339 : ℕ)^32*10000000000000000^133 ≤ 10006932014890919^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50144213604214029339 50000000000000000000 10006932014890919 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006932014890919/10000000000000000 : ℝ)) (X := (50144213604214029339/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3467902622397/2072300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1732056134261/1036150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (20723/100000 : ℝ)) (alpha := (3467902622397/2072300000000000 : ℝ)) (beta := (1732056134261/1036150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20723/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3467902622397/2072300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1732056134261/1036150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (243/50000 : ℝ) ^ (133/32 : ℝ) ≤ (12135341393/50000000000000000000 : ℝ) := by
    have hpowers : (243/50000 : ℝ)^133 ≤ (12135341393/50000000000000000000 : ℝ)^32 := by
      have hnat : (243 : ℕ)^133*50000000000000000000^32 ≤ 12135341393^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        243 50000 12135341393 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (243/50000 : ℝ)) (X := (12135341393/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50000000012135341393/50000000000000000000 : ℝ) ≤ (10000000000583957/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50000000012135341393/50000000000000000000 : ℝ)^32 ≤ (10000000000583957/10000000000000000 : ℝ)^133 := by
      have hnat : (50000000012135341393 : ℕ)^32*10000000000000000^133 ≤ 10000000000583957^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000012135341393 50000000000000000000 10000000000583957 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000583957/10000000000000000 : ℝ)) (X := (50000000012135341393/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25000000012135341393/25000000000000000000 : ℝ) ≤ (10000000001167913/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25000000012135341393/25000000000000000000 : ℝ)^32 ≤ (10000000001167913/10000000000000000 : ℝ)^133 := by
      have hnat : (25000000012135341393 : ℕ)^32*10000000000000000^133 ≤ 10000000001167913^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000012135341393 25000000000000000000 10000000001167913 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001167913/10000000000000000 : ℝ)) (X := (25000000012135341393/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(583957/48600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(5407/450000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (243/50000 : ℝ)) (alpha := (583957/48600000000000 : ℝ)) (beta := (5407/450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (243/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(583957/48600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(5407/450000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10191/100000 : ℝ) ^ (133/32 : ℝ) ≤ (7549202613911913/100000000000000000000 : ℝ) := by
    have hpowers : (10191/100000 : ℝ)^133 ≤ (7549202613911913/100000000000000000000 : ℝ)^32 := by
      have hnat : (10191 : ℕ)^133*100000000000000000000^32 ≤ 7549202613911913^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10191 100000 7549202613911913 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10191/100000 : ℝ)) (X := (7549202613911913/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100007549202613911913/100000000000000000000 : ℝ) ≤ (2500045407435977/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (100007549202613911913/100000000000000000000 : ℝ)^32 ≤ (2500045407435977/2500000000000000 : ℝ)^133 := by
      have hnat : (100007549202613911913 : ℕ)^32*2500000000000000^133 ≤ 2500045407435977^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100007549202613911913 100000000000000000000 2500045407435977 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500045407435977/2500000000000000 : ℝ)) (X := (100007549202613911913/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50007549202613911913/50000000000000000000 : ℝ) ≤ (10000363249076333/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50007549202613911913/50000000000000000000 : ℝ)^32 ≤ (10000363249076333/10000000000000000 : ℝ)^133 := by
      have hnat : (50007549202613911913 : ℕ)^32*10000000000000000^133 ≤ 10000363249076333^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007549202613911913 50000000000000000000 10000363249076333 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000363249076333/10000000000000000 : ℝ)) (X := (50007549202613911913/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(45407435977/254775000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2421591099/13588000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (10191/100000 : ℝ)) (alpha := (45407435977/254775000000000 : ℝ)) (beta := (2421591099/13588000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (10191/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(45407435977/254775000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2421591099/13588000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-305037023/625000000 : ℝ)*X 0 0+(4051446633/10000000000 : ℝ)*X 0 1+(50643231/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4193115851/10000000000 : ℝ)*X 1 0+(-435095369/1250000000 : ℝ)*X 1 1+(329219949/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2096553397/5000000000 : ℝ)*X 2 0+(32922033/62500000 : ℝ)*X 2 1+(-870191403/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1847395541/5000000000 : ℝ)*X 0 0+(4641523907/10000000000 : ℝ)*X 0 1+(464150851/1000000000 : ℝ)*X 0 2+(1847395541/5000000000 : ℝ)*X 1 0+(4641523907/10000000000 : ℝ)*X 1 1+(464150851/1000000000 : ℝ)*X 1 2+(1847395541/5000000000 : ℝ)*X 2 0+(4641523907/10000000000 : ℝ)*X 2 1+(464150851/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305077_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-5350774629380493483098828185033/879950387500000000000000000000 : ℝ) := by norm_num
    linear_combination (65713/500000000000 : ℝ)*(base11) + (4663/62500000000 : ℝ)*(base19) + (62447/500000000000 : ℝ)*(base23) + (886112539/1600000000 : ℝ)*(base49) + (12196490321/50000000000 : ℝ)*(base50) + (4163/1000000000000 : ℝ)*(base53) + (8176629551/125000000000 : ℝ)*(base59) + (309616136809/1000000000000 : ℝ)*(base60) + (4779/3125 : ℝ)*(major_s1_0) + (4779/3125 : ℝ)*(major_s1_1) + (1529279995837/1000000000000 : ℝ)*(major_s1_2) + (81076908387/40000000000 : ℝ)*(sp_s1_0) + (2026922766493/1000000000000 : ℝ)*(sp_s1_1) + (2026922720371/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (405384569053/200000000000 : ℝ)*(f.sum) + (38222559063251/254775000000000000000000000 : ℝ)*base63 + (2817681569993/13588000000000000000000000 : ℝ)*base65 + (1260809/15000000000000000000 : ℝ)*base67 + (139285833375937/509550000000000000000000000 : ℝ)*base69 + (181877011933483423/1407920620000000000000000000000 : ℝ)*base70 + (5569635176389/12951875000000000000000000 : ℝ)*base73 + (1045150287/5000000000000000000000 : ℝ)*base74 + (281779417689/1295187500000000000000000 : ℝ)*base76 + (6276410377303/155422500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p005_b033 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=77 := by omega
  rcases hc with rfl
  · exact collision_c305077 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
