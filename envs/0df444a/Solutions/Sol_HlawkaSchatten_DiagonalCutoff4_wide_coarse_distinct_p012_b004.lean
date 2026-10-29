-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b004
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:06.86932+00:00
-- url     : https://prove2.me/submissions/f0521f20-94f5-4610-aa22-8067d53d805f

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
theorem collision_support_c312009_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (212595101/500000000 : ℝ)*x 0 + (1175973447/2500000000 : ℝ)*x 1 + (3709161229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212595101/500000000 : ℝ)^37 ≤ (3358330661383/10000000000000 : ℝ)^29 := by
    have hnat : (212595101 : ℕ)^37*10000000000000^29 ≤ 3358330661383^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212595101 500000000 3358330661383 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1175973447/2500000000 : ℝ)^37 ≤ (477541336111/1250000000000 : ℝ)^29 := by
    have hnat : (1175973447 : ℕ)^37*1250000000000^29 ≤ 477541336111^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175973447 2500000000 477541336111 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709161229/10000000000 : ℝ)^37 ≤ (28213386487897/100000000000000 : ℝ)^29 := by
    have hnat : (3709161229 : ℕ)^37*100000000000000^29 ≤ 28213386487897^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709161229 10000000000 28213386487897 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212595101/500000000 : ℝ), (1175973447/2500000000 : ℝ), (3709161229/10000000000 : ℝ)] ![(3358330661383/10000000000000 : ℝ), (477541336111/1250000000000 : ℝ), (28213386487897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212595101/500000000 : ℝ)|^37 ≤ (3358330661383/10000000000000 : ℝ)^29
        have hw : |(212595101/500000000 : ℝ)|=(212595101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1175973447/2500000000 : ℝ)|^37 ≤ (477541336111/1250000000000 : ℝ)^29
        have hw : |(1175973447/2500000000 : ℝ)|=(1175973447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709161229/10000000000 : ℝ)|^37 ≤ (28213386487897/100000000000000 : ℝ)^29
        have hw : |(3709161229/10000000000 : ℝ)|=(3709161229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1080502089/2000000000 : ℝ)*x 0 + (-890173991/2000000000 : ℝ)*x 1 + (-1349907381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080502089/2000000000 : ℝ)^37 ≤ (569821591509/1250000000000 : ℝ)^29 := by
    have hnat : (1080502089 : ℕ)^37*1250000000000^29 ≤ 569821591509^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080502089 2000000000 569821591509 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890173991/2000000000 : ℝ)^37 ≤ (17800581664611/50000000000000 : ℝ)^29 := by
    have hnat : (890173991 : ℕ)^37*50000000000000^29 ≤ 17800581664611^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890173991 2000000000 17800581664611 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349907381/5000000000 : ℝ)^37 ≤ (9406554666153/50000000000000 : ℝ)^29 := by
    have hnat : (1349907381 : ℕ)^37*50000000000000^29 ≤ 9406554666153^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349907381 5000000000 9406554666153 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080502089/2000000000 : ℝ), (-890173991/2000000000 : ℝ), (-1349907381/5000000000 : ℝ)] ![(569821591509/1250000000000 : ℝ), (17800581664611/50000000000000 : ℝ), (9406554666153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080502089/2000000000 : ℝ)|^37 ≤ (569821591509/1250000000000 : ℝ)^29
        have hw : |(1080502089/2000000000 : ℝ)|=(1080502089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890173991/2000000000 : ℝ)|^37 ≤ (17800581664611/50000000000000 : ℝ)^29
        have hw : |(-890173991/2000000000 : ℝ)|=(890173991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1349907381/5000000000 : ℝ)|^37 ≤ (9406554666153/50000000000000 : ℝ)^29
        have hw : |(-1349907381/5000000000 : ℝ)|=(1349907381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4054211863/10000000000 : ℝ)*x 0 + (-5752399483/10000000000 : ℝ)*x 1 + (680493329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4054211863/10000000000 : ℝ)^37 ≤ (31604047032521/100000000000000 : ℝ)^29 := by
    have hnat : (4054211863 : ℕ)^37*100000000000000^29 ≤ 31604047032521^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4054211863 10000000000 31604047032521 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5752399483/10000000000 : ℝ)^37 ≤ (24692809267113/50000000000000 : ℝ)^29 := by
    have hnat : (5752399483 : ℕ)^37*50000000000000^29 ≤ 24692809267113^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5752399483 10000000000 24692809267113 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680493329/2500000000 : ℝ)^37 ≤ (4752583604567/25000000000000 : ℝ)^29 := by
    have hnat : (680493329 : ℕ)^37*25000000000000^29 ≤ 4752583604567^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680493329 2500000000 4752583604567 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4054211863/10000000000 : ℝ), (-5752399483/10000000000 : ℝ), (680493329/2500000000 : ℝ)] ![(31604047032521/100000000000000 : ℝ), (24692809267113/50000000000000 : ℝ), (4752583604567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4054211863/10000000000 : ℝ)|^37 ≤ (31604047032521/100000000000000 : ℝ)^29
        have hw : |(-4054211863/10000000000 : ℝ)|=(4054211863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5752399483/10000000000 : ℝ)|^37 ≤ (24692809267113/50000000000000 : ℝ)^29
        have hw : |(-5752399483/10000000000 : ℝ)|=(5752399483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680493329/2500000000 : ℝ)|^37 ≤ (4752583604567/25000000000000 : ℝ)^29
        have hw : |(680493329/2500000000 : ℝ)|=(680493329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (312150879/1000000000 : ℝ)*x 0 + (6323202867/10000000000 : ℝ)*x 1 + (3012721089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312150879/1000000000 : ℝ)^37 ≤ (4528026083/20000000000 : ℝ)^29 := by
    have hnat : (312150879 : ℕ)^37*20000000000^29 ≤ 4528026083^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312150879 1000000000 4528026083 20000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6323202867/10000000000 : ℝ)^37 ≤ (27860776774963/50000000000000 : ℝ)^29 := by
    have hnat : (6323202867 : ℕ)^37*50000000000000^29 ≤ 27860776774963^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6323202867 10000000000 27860776774963 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3012721089/10000000000 : ℝ)^37 ≤ (10819158010679/50000000000000 : ℝ)^29 := by
    have hnat : (3012721089 : ℕ)^37*50000000000000^29 ≤ 10819158010679^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012721089 10000000000 10819158010679 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(312150879/1000000000 : ℝ), (6323202867/10000000000 : ℝ), (3012721089/10000000000 : ℝ)] ![(4528026083/20000000000 : ℝ), (27860776774963/50000000000000 : ℝ), (10819158010679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(312150879/1000000000 : ℝ)|^37 ≤ (4528026083/20000000000 : ℝ)^29
        have hw : |(312150879/1000000000 : ℝ)|=(312150879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6323202867/10000000000 : ℝ)|^37 ≤ (27860776774963/50000000000000 : ℝ)^29
        have hw : |(6323202867/10000000000 : ℝ)|=(6323202867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3012721089/10000000000 : ℝ)|^37 ≤ (10819158010679/50000000000000 : ℝ)^29
        have hw : |(3012721089/10000000000 : ℝ)|=(3012721089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (211701037/312500000 : ℝ)*x 0 + (-57302491/125000000 : ℝ)*x 1 + (-500104181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211701037/312500000 : ℝ)^37 ≤ (60843926012023/100000000000000 : ℝ)^29 := by
    have hnat : (211701037 : ℕ)^37*100000000000000^29 ≤ 60843926012023^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211701037 312500000 60843926012023 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57302491/125000000 : ℝ)^37 ≤ (36967402298343/100000000000000 : ℝ)^29 := by
    have hnat : (57302491 : ℕ)^37*100000000000000^29 ≤ 36967402298343^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57302491 125000000 36967402298343 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500104181/10000000000 : ℝ)^37 ≤ (2188671684091/100000000000000 : ℝ)^29 := by
    have hnat : (500104181 : ℕ)^37*100000000000000^29 ≤ 2188671684091^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500104181 10000000000 2188671684091 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211701037/312500000 : ℝ), (-57302491/125000000 : ℝ), (-500104181/10000000000 : ℝ)] ![(60843926012023/100000000000000 : ℝ), (36967402298343/100000000000000 : ℝ), (2188671684091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211701037/312500000 : ℝ)|^37 ≤ (60843926012023/100000000000000 : ℝ)^29
        have hw : |(211701037/312500000 : ℝ)|=(211701037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57302491/125000000 : ℝ)|^37 ≤ (36967402298343/100000000000000 : ℝ)^29
        have hw : |(-57302491/125000000 : ℝ)|=(57302491/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500104181/10000000000 : ℝ)|^37 ≤ (2188671684091/100000000000000 : ℝ)^29
        have hw : |(-500104181/10000000000 : ℝ)|=(500104181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-69484583/10000000000 : ℝ)*x 0 + (-9417343/80000000 : ℝ)*x 1 + (4735457833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69484583/10000000000 : ℝ)^37 ≤ (22052475731/12500000000000 : ℝ)^29 := by
    have hnat : (69484583 : ℕ)^37*12500000000000^29 ≤ 22052475731^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69484583 10000000000 22052475731 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9417343/80000000 : ℝ)^37 ≤ (3262030107141/50000000000000 : ℝ)^29 := by
    have hnat : (9417343 : ℕ)^37*50000000000000^29 ≤ 3262030107141^29*80000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9417343 80000000 3262030107141 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4735457833/5000000000 : ℝ)^37 ≤ (46649759985111/50000000000000 : ℝ)^29 := by
    have hnat : (4735457833 : ℕ)^37*50000000000000^29 ≤ 46649759985111^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735457833 5000000000 46649759985111 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69484583/10000000000 : ℝ), (-9417343/80000000 : ℝ), (4735457833/5000000000 : ℝ)] ![(22052475731/12500000000000 : ℝ), (3262030107141/50000000000000 : ℝ), (46649759985111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69484583/10000000000 : ℝ)|^37 ≤ (22052475731/12500000000000 : ℝ)^29
        have hw : |(-69484583/10000000000 : ℝ)|=(69484583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9417343/80000000 : ℝ)|^37 ≤ (3262030107141/50000000000000 : ℝ)^29
        have hw : |(-9417343/80000000 : ℝ)|=(9417343/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4735457833/5000000000 : ℝ)|^37 ≤ (46649759985111/50000000000000 : ℝ)^29
        have hw : |(4735457833/5000000000 : ℝ)|=(4735457833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-163502807/312500000 : ℝ)*x 0 + (-4091830239/10000000000 : ℝ)*x 1 + (659096057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163502807/312500000 : ℝ)^37 ≤ (43759096605397/100000000000000 : ℝ)^29 := by
    have hnat : (163502807 : ℕ)^37*100000000000000^29 ≤ 43759096605397^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163502807 312500000 43759096605397 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4091830239/10000000000 : ℝ)^37 ≤ (15989334940641/50000000000000 : ℝ)^29 := by
    have hnat : (4091830239 : ℕ)^37*50000000000000^29 ≤ 15989334940641^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4091830239 10000000000 15989334940641 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659096057/2000000000 : ℝ)^37 ≤ (2426223349291/10000000000000 : ℝ)^29 := by
    have hnat : (659096057 : ℕ)^37*10000000000000^29 ≤ 2426223349291^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659096057 2000000000 2426223349291 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-163502807/312500000 : ℝ), (-4091830239/10000000000 : ℝ), (659096057/2000000000 : ℝ)] ![(43759096605397/100000000000000 : ℝ), (15989334940641/50000000000000 : ℝ), (2426223349291/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-163502807/312500000 : ℝ)|^37 ≤ (43759096605397/100000000000000 : ℝ)^29
        have hw : |(-163502807/312500000 : ℝ)|=(163502807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4091830239/10000000000 : ℝ)|^37 ≤ (15989334940641/50000000000000 : ℝ)^29
        have hw : |(-4091830239/10000000000 : ℝ)|=(4091830239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659096057/2000000000 : ℝ)|^37 ≤ (2426223349291/10000000000000 : ℝ)^29
        have hw : |(659096057/2000000000 : ℝ)|=(659096057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (316566067/500000000 : ℝ)*x 0 + (1972673341/5000000000 : ℝ)*x 1 + (2100998071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316566067/500000000 : ℝ)^37 ≤ (55812847302143/100000000000000 : ℝ)^29 := by
    have hnat : (316566067 : ℕ)^37*100000000000000^29 ≤ 55812847302143^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316566067 500000000 55812847302143 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972673341/5000000000 : ℝ)^37 ≤ (6105066325077/20000000000000 : ℝ)^29 := by
    have hnat : (1972673341 : ℕ)^37*20000000000000^29 ≤ 6105066325077^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972673341 5000000000 6105066325077 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100998071/10000000000 : ℝ)^37 ≤ (13661821056221/100000000000000 : ℝ)^29 := by
    have hnat : (2100998071 : ℕ)^37*100000000000000^29 ≤ 13661821056221^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100998071 10000000000 13661821056221 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(316566067/500000000 : ℝ), (1972673341/5000000000 : ℝ), (2100998071/10000000000 : ℝ)] ![(55812847302143/100000000000000 : ℝ), (6105066325077/20000000000000 : ℝ), (13661821056221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(316566067/500000000 : ℝ)|^37 ≤ (55812847302143/100000000000000 : ℝ)^29
        have hw : |(316566067/500000000 : ℝ)|=(316566067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1972673341/5000000000 : ℝ)|^37 ≤ (6105066325077/20000000000000 : ℝ)^29
        have hw : |(1972673341/5000000000 : ℝ)|=(1972673341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2100998071/10000000000 : ℝ)|^37 ≤ (13661821056221/100000000000000 : ℝ)^29
        have hw : |(2100998071/10000000000 : ℝ)|=(2100998071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6617998097/10000000000 : ℝ)*x 0 + (-2360721463/5000000000 : ℝ)*x 1 + (-282530817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6617998097/10000000000 : ℝ)^37 ≤ (7382134104843/12500000000000 : ℝ)^29 := by
    have hnat : (6617998097 : ℕ)^37*12500000000000^29 ≤ 7382134104843^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6617998097 10000000000 7382134104843 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2360721463/5000000000 : ℝ)^37 ≤ (38385246050957/100000000000000 : ℝ)^29 := by
    have hnat : (2360721463 : ℕ)^37*100000000000000^29 ≤ 38385246050957^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360721463 5000000000 38385246050957 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282530817/5000000000 : ℝ)^37 ≤ (2557681088453/100000000000000 : ℝ)^29 := by
    have hnat : (282530817 : ℕ)^37*100000000000000^29 ≤ 2557681088453^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282530817 5000000000 2557681088453 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6617998097/10000000000 : ℝ), (-2360721463/5000000000 : ℝ), (-282530817/5000000000 : ℝ)] ![(7382134104843/12500000000000 : ℝ), (38385246050957/100000000000000 : ℝ), (2557681088453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6617998097/10000000000 : ℝ)|^37 ≤ (7382134104843/12500000000000 : ℝ)^29
        have hw : |(6617998097/10000000000 : ℝ)|=(6617998097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2360721463/5000000000 : ℝ)|^37 ≤ (38385246050957/100000000000000 : ℝ)^29
        have hw : |(-2360721463/5000000000 : ℝ)|=(2360721463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282530817/5000000000 : ℝ)|^37 ≤ (2557681088453/100000000000000 : ℝ)^29
        have hw : |(-282530817/5000000000 : ℝ)|=(282530817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-12647509/2500000000 : ℝ)*x 0 + (-24978583/250000000 : ℝ)*x 1 + (1196677563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12647509/2500000000 : ℝ)^37 ≤ (117680256401/100000000000000 : ℝ)^29 := by
    have hnat : (12647509 : ℕ)^37*100000000000000^29 ≤ 117680256401^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12647509 2500000000 117680256401 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24978583/250000000 : ℝ)^37 ≤ (2646263250553/50000000000000 : ℝ)^29 := by
    have hnat : (24978583 : ℕ)^37*50000000000000^29 ≤ 2646263250553^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24978583 250000000 2646263250553 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196677563/1250000000 : ℝ)^37 ≤ (47294896614683/50000000000000 : ℝ)^29 := by
    have hnat : (1196677563 : ℕ)^37*50000000000000^29 ≤ 47294896614683^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196677563 1250000000 47294896614683 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12647509/2500000000 : ℝ), (-24978583/250000000 : ℝ), (1196677563/1250000000 : ℝ)] ![(117680256401/100000000000000 : ℝ), (2646263250553/50000000000000 : ℝ), (47294896614683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12647509/2500000000 : ℝ)|^37 ≤ (117680256401/100000000000000 : ℝ)^29
        have hw : |(-12647509/2500000000 : ℝ)|=(12647509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24978583/250000000 : ℝ)|^37 ≤ (2646263250553/50000000000000 : ℝ)^29
        have hw : |(-24978583/250000000 : ℝ)|=(24978583/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196677563/1250000000 : ℝ)|^37 ≤ (47294896614683/50000000000000 : ℝ)^29
        have hw : |(1196677563/1250000000 : ℝ)|=(1196677563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4280797489/10000000000 : ℝ)*x 0 + (-4812494559/10000000000 : ℝ)*x 1 + (35619909/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280797489/10000000000 : ℝ)^37 ≤ (33874767255533/100000000000000 : ℝ)^29 := by
    have hnat : (4280797489 : ℕ)^37*100000000000000^29 ≤ 33874767255533^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280797489 10000000000 33874767255533 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4812494559/10000000000 : ℝ)^37 ≤ (19666100592419/50000000000000 : ℝ)^29 := by
    have hnat : (4812494559 : ℕ)^37*50000000000000^29 ≤ 19666100592419^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4812494559 10000000000 19666100592419 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35619909/100000000 : ℝ)^37 ≤ (26793031547/100000000000 : ℝ)^29 := by
    have hnat : (35619909 : ℕ)^37*100000000000^29 ≤ 26793031547^29*100000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35619909 100000000 26793031547 100000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4280797489/10000000000 : ℝ), (-4812494559/10000000000 : ℝ), (35619909/100000000 : ℝ)] ![(33874767255533/100000000000000 : ℝ), (19666100592419/50000000000000 : ℝ), (26793031547/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4280797489/10000000000 : ℝ)|^37 ≤ (33874767255533/100000000000000 : ℝ)^29
        have hw : |(-4280797489/10000000000 : ℝ)|=(4280797489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4812494559/10000000000 : ℝ)|^37 ≤ (19666100592419/50000000000000 : ℝ)^29
        have hw : |(-4812494559/10000000000 : ℝ)|=(4812494559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35619909/100000000 : ℝ)|^37 ≤ (26793031547/100000000000 : ℝ)^29
        have hw : |(35619909/100000000 : ℝ)|=(35619909/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3474625089/10000000000 : ℝ)*x 0 + (2377423839/5000000000 : ℝ)*x 1 + (2211180349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3474625089/10000000000 : ℝ)^37 ≤ (5191488119059/20000000000000 : ℝ)^29 := by
    have hnat : (3474625089 : ℕ)^37*20000000000000^29 ≤ 5191488119059^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3474625089 10000000000 5191488119059 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2377423839/5000000000 : ℝ)^37 ≤ (19366041139101/50000000000000 : ℝ)^29 := by
    have hnat : (2377423839 : ℕ)^37*50000000000000^29 ≤ 19366041139101^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377423839 5000000000 19366041139101 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211180349/5000000000 : ℝ)^37 ≤ (8827619276659/25000000000000 : ℝ)^29 := by
    have hnat : (2211180349 : ℕ)^37*25000000000000^29 ≤ 8827619276659^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211180349 5000000000 8827619276659 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3474625089/10000000000 : ℝ), (2377423839/5000000000 : ℝ), (2211180349/5000000000 : ℝ)] ![(5191488119059/20000000000000 : ℝ), (19366041139101/50000000000000 : ℝ), (8827619276659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3474625089/10000000000 : ℝ)|^37 ≤ (5191488119059/20000000000000 : ℝ)^29
        have hw : |(3474625089/10000000000 : ℝ)|=(3474625089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2377423839/5000000000 : ℝ)|^37 ≤ (19366041139101/50000000000000 : ℝ)^29
        have hw : |(2377423839/5000000000 : ℝ)|=(2377423839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2211180349/5000000000 : ℝ)|^37 ≤ (8827619276659/25000000000000 : ℝ)^29
        have hw : |(2211180349/5000000000 : ℝ)|=(2211180349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s0_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5818757297/10000000000 : ℝ)*x 0 + (-88448827/250000000 : ℝ)*x 1 + (-3195152541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5818757297/10000000000 : ℝ)^37 ≤ (25056812983269/50000000000000 : ℝ)^29 := by
    have hnat : (5818757297 : ℕ)^37*50000000000000^29 ≤ 25056812983269^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5818757297 10000000000 25056812983269 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88448827/250000000 : ℝ)^37 ≤ (415039954893/1562500000000 : ℝ)^29 := by
    have hnat : (88448827 : ℕ)^37*1562500000000^29 ≤ 415039954893^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88448827 250000000 415039954893 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3195152541/10000000000 : ℝ)^37 ≤ (932952676243/4000000000000 : ℝ)^29 := by
    have hnat : (3195152541 : ℕ)^37*4000000000000^29 ≤ 932952676243^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195152541 10000000000 932952676243 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5818757297/10000000000 : ℝ), (-88448827/250000000 : ℝ), (-3195152541/10000000000 : ℝ)] ![(25056812983269/50000000000000 : ℝ), (415039954893/1562500000000 : ℝ), (932952676243/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5818757297/10000000000 : ℝ)|^37 ≤ (25056812983269/50000000000000 : ℝ)^29
        have hw : |(5818757297/10000000000 : ℝ)|=(5818757297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88448827/250000000 : ℝ)|^37 ≤ (415039954893/1562500000000 : ℝ)^29
        have hw : |(-88448827/250000000 : ℝ)|=(88448827/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3195152541/10000000000 : ℝ)|^37 ≤ (932952676243/4000000000000 : ℝ)^29
        have hw : |(-3195152541/10000000000 : ℝ)|=(3195152541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4227076271/10000000000 : ℝ)*x 0 + (-422707639/1000000000 : ℝ)*x 1 + (4227076547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076271/10000000000 : ℝ)^37 ≤ (33333332002939/100000000000000 : ℝ)^29 := by
    have hnat : (4227076271 : ℕ)^37*100000000000000^29 ≤ 33333332002939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076271 10000000000 33333332002939 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422707639/1000000000 : ℝ)^37 ≤ (33333333200201/100000000000000 : ℝ)^29 := by
    have hnat : (422707639 : ℕ)^37*100000000000000^29 ≤ 33333333200201^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422707639 1000000000 33333333200201 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076547/10000000000 : ℝ)^37 ≤ (33333334779783/100000000000000 : ℝ)^29 := by
    have hnat : (4227076547 : ℕ)^37*100000000000000^29 ≤ 33333334779783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076547 10000000000 33333334779783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4227076271/10000000000 : ℝ), (-422707639/1000000000 : ℝ), (4227076547/10000000000 : ℝ)] ![(33333332002939/100000000000000 : ℝ), (33333333200201/100000000000000 : ℝ), (33333334779783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4227076271/10000000000 : ℝ)|^37 ≤ (33333332002939/100000000000000 : ℝ)^29
        have hw : |(-4227076271/10000000000 : ℝ)|=(4227076271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422707639/1000000000 : ℝ)|^37 ≤ (33333333200201/100000000000000 : ℝ)^29
        have hw : |(-422707639/1000000000 : ℝ)|=(422707639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227076547/10000000000 : ℝ)|^37 ≤ (33333334779783/100000000000000 : ℝ)^29
        have hw : |(4227076547/10000000000 : ℝ)|=(4227076547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076271/10000000000 : ℝ)*x 0 + (422707639/1000000000 : ℝ)*x 1 + (4227076547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076271/10000000000 : ℝ)^37 ≤ (33333332002939/100000000000000 : ℝ)^29 := by
    have hnat : (4227076271 : ℕ)^37*100000000000000^29 ≤ 33333332002939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076271 10000000000 33333332002939 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422707639/1000000000 : ℝ)^37 ≤ (33333333200201/100000000000000 : ℝ)^29 := by
    have hnat : (422707639 : ℕ)^37*100000000000000^29 ≤ 33333333200201^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422707639 1000000000 33333333200201 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076547/10000000000 : ℝ)^37 ≤ (33333334779783/100000000000000 : ℝ)^29 := by
    have hnat : (4227076547 : ℕ)^37*100000000000000^29 ≤ 33333334779783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076547 10000000000 33333334779783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076271/10000000000 : ℝ), (422707639/1000000000 : ℝ), (4227076547/10000000000 : ℝ)] ![(33333332002939/100000000000000 : ℝ), (33333333200201/100000000000000 : ℝ), (33333334779783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076271/10000000000 : ℝ)|^37 ≤ (33333332002939/100000000000000 : ℝ)^29
        have hw : |(4227076271/10000000000 : ℝ)|=(4227076271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422707639/1000000000 : ℝ)|^37 ≤ (33333333200201/100000000000000 : ℝ)^29
        have hw : |(422707639/1000000000 : ℝ)|=(422707639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227076547/10000000000 : ℝ)|^37 ≤ (33333334779783/100000000000000 : ℝ)^29
        have hw : |(4227076547/10000000000 : ℝ)|=(4227076547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076271/10000000000 : ℝ)*x 0 + (-422707639/1000000000 : ℝ)*x 1 + (-4227076547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076271/10000000000 : ℝ)^37 ≤ (33333332002939/100000000000000 : ℝ)^29 := by
    have hnat : (4227076271 : ℕ)^37*100000000000000^29 ≤ 33333332002939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076271 10000000000 33333332002939 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422707639/1000000000 : ℝ)^37 ≤ (33333333200201/100000000000000 : ℝ)^29 := by
    have hnat : (422707639 : ℕ)^37*100000000000000^29 ≤ 33333333200201^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422707639 1000000000 33333333200201 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076547/10000000000 : ℝ)^37 ≤ (33333334779783/100000000000000 : ℝ)^29 := by
    have hnat : (4227076547 : ℕ)^37*100000000000000^29 ≤ 33333334779783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076547 10000000000 33333334779783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076271/10000000000 : ℝ), (-422707639/1000000000 : ℝ), (-4227076547/10000000000 : ℝ)] ![(33333332002939/100000000000000 : ℝ), (33333333200201/100000000000000 : ℝ), (33333334779783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076271/10000000000 : ℝ)|^37 ≤ (33333332002939/100000000000000 : ℝ)^29
        have hw : |(4227076271/10000000000 : ℝ)|=(4227076271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422707639/1000000000 : ℝ)|^37 ≤ (33333333200201/100000000000000 : ℝ)^29
        have hw : |(-422707639/1000000000 : ℝ)|=(422707639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4227076547/10000000000 : ℝ)|^37 ≤ (33333334779783/100000000000000 : ℝ)^29
        have hw : |(-4227076547/10000000000 : ℝ)|=(4227076547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312009_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076271/10000000000 : ℝ)*x 0 + (-422707639/1000000000 : ℝ)*x 1 + (4227076547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076271/10000000000 : ℝ)^37 ≤ (33333332002939/100000000000000 : ℝ)^29 := by
    have hnat : (4227076271 : ℕ)^37*100000000000000^29 ≤ 33333332002939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076271 10000000000 33333332002939 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422707639/1000000000 : ℝ)^37 ≤ (33333333200201/100000000000000 : ℝ)^29 := by
    have hnat : (422707639 : ℕ)^37*100000000000000^29 ≤ 33333333200201^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422707639 1000000000 33333333200201 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076547/10000000000 : ℝ)^37 ≤ (33333334779783/100000000000000 : ℝ)^29 := by
    have hnat : (4227076547 : ℕ)^37*100000000000000^29 ≤ 33333334779783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076547 10000000000 33333334779783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076271/10000000000 : ℝ), (-422707639/1000000000 : ℝ), (4227076547/10000000000 : ℝ)] ![(33333332002939/100000000000000 : ℝ), (33333333200201/100000000000000 : ℝ), (33333334779783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076271/10000000000 : ℝ)|^37 ≤ (33333332002939/100000000000000 : ℝ)^29
        have hw : |(4227076271/10000000000 : ℝ)|=(4227076271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422707639/1000000000 : ℝ)|^37 ≤ (33333333200201/100000000000000 : ℝ)^29
        have hw : |(-422707639/1000000000 : ℝ)|=(422707639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227076547/10000000000 : ℝ)|^37 ≤ (33333334779783/100000000000000 : ℝ)^29
        have hw : |(4227076547/10000000000 : ℝ)|=(4227076547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312009 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((212595101/500000000 : ℝ)*X 1 0+(1175973447/2500000000 : ℝ)*X 1 1+(3709161229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1080502089/2000000000 : ℝ)*X 2 0+(-890173991/2000000000 : ℝ)*X 2 1+(-1349907381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-4054211863/10000000000 : ℝ)*X 0 0+(-5752399483/10000000000 : ℝ)*X 0 1+(680493329/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((312150879/1000000000 : ℝ)*X 1 0+(6323202867/10000000000 : ℝ)*X 1 1+(3012721089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((211701037/312500000 : ℝ)*X 2 0+(-57302491/125000000 : ℝ)*X 2 1+(-500104181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-69484583/10000000000 : ℝ)*X 0 0+(-9417343/80000000 : ℝ)*X 0 1+(4735457833/5000000000 : ℝ)*X 0 2+(-69484583/10000000000 : ℝ)*X 1 0+(-9417343/80000000 : ℝ)*X 1 1+(4735457833/5000000000 : ℝ)*X 1 2+(-69484583/10000000000 : ℝ)*X 2 0+(-9417343/80000000 : ℝ)*X 2 1+(4735457833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-163502807/312500000 : ℝ)*X 0 0+(-4091830239/10000000000 : ℝ)*X 0 1+(659096057/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((316566067/500000000 : ℝ)*X 1 0+(1972673341/5000000000 : ℝ)*X 1 1+(2100998071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6617998097/10000000000 : ℝ)*X 2 0+(-2360721463/5000000000 : ℝ)*X 2 1+(-282530817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-12647509/2500000000 : ℝ)*X 0 0+(-24978583/250000000 : ℝ)*X 0 1+(1196677563/1250000000 : ℝ)*X 0 2+(-12647509/2500000000 : ℝ)*X 1 0+(-24978583/250000000 : ℝ)*X 1 1+(1196677563/1250000000 : ℝ)*X 1 2+(-12647509/2500000000 : ℝ)*X 2 0+(-24978583/250000000 : ℝ)*X 2 1+(1196677563/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4280797489/10000000000 : ℝ)*X 0 0+(-4812494559/10000000000 : ℝ)*X 0 1+(35619909/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3474625089/10000000000 : ℝ)*X 1 0+(2377423839/5000000000 : ℝ)*X 1 1+(2211180349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((5818757297/10000000000 : ℝ)*X 2 0+(-88448827/250000000 : ℝ)*X 2 1+(-3195152541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((57893/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57893/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4145249572400141429853/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31951945769/500000000000 : ℝ)*(base1) + (367251536047/1000000000000 : ℝ)*(base7) + (382659/100000000000 : ℝ)*(base40) + (820087/250000000000 : ℝ)*(base43) + (71418343949/1000000000000 : ℝ)*(base50) + (113439693613/100000000000 : ℝ)*(base54) + (151904011119/250000000000 : ℝ)*(base60) + (584047087263/250000000000 : ℝ)*(major_s0_0) + (2336185068703/1000000000000 : ℝ)*(major_s0_1) + (600895706461/500000000000 : ℝ)*(major_s0_2) + (3118385022109/1000000000000 : ℝ)*(sp_s0_7) + (3054484410919/1000000000000 : ℝ)*(sp_s0_8) + (1920084194441/1000000000000 : ℝ)*(sp_s0_9) + (568595043483/1000000000000 : ℝ)*(sp_s0_13) + (1366840171/976562500 : ℝ)*(f.failure) + (3054484410919/1000000000000 : ℝ)*(f.sum) + (3542787326299/40000000000000000000000000 : ℝ)*base62 + (2149151761087289/5000000000000000000000000000 : ℝ)*base65 + (4590035107062547/10000000000000000000000000000 : ℝ)*base66 + (851099445203237/2500000000000000000000000000 : ℝ)*base69 + (485367446331079/1000000000000000000000000000 : ℝ)*base70 + (1189535097706013/2500000000000000000000000000 : ℝ)*base73 + (2240629622193849/5000000000000000000000000000 : ℝ)*base74 + (457250942439329/1250000000000000000000000000 : ℝ)*base77 + (518743596447699/2000000000000000000000000000 : ℝ)*base78 + (109/781250000000000 : ℝ)*base87 + (3561/3125000000000000 : ℝ)*base89 + (109/781250000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-73759/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-73759/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (91823091511662873732867/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (584447546633/1000000000000 : ℝ)*(base1) + (129035448049/200000000000 : ℝ)*(base7) + (566675225439/1000000000000 : ℝ)*(base40) + (3223911/500000000000 : ℝ)*(base50) + (1482012696437/1000000000000 : ℝ)*(base54) + (177894966663/500000000000 : ℝ)*(base60) + (2509145530191/1000000000000 : ℝ)*(major_s0_0) + (2509145530191/1000000000000 : ℝ)*(major_s0_1) + (1027132833753/1000000000000 : ℝ)*(major_s0_2) + (8111999/25000000000 : ℝ)*(sp_s0_9) + (3716057515191/1000000000000 : ℝ)*(sp_s0_14) + (1565804984279/500000000000 : ℝ)*(sp_s0_15) + (10307954951/6250000000 : ℝ)*(sp_s0_16) + (20495622223/250000000000 : ℝ)*(sp_s0_20) + (751632745859/500000000000 : ℝ)*(f.failure) + (1565804984279/500000000000 : ℝ)*(f.sum) + (1251340387581/625000000000000000000000000 : ℝ)*base63 + (6370482746515003/10000000000000000000000000000 : ℝ)*base64 + (4160437247701059/10000000000000000000000000000 : ℝ)*base66 + (3300079710282001/5000000000000000000000000000 : ℝ)*base69 + (2404685873152297/10000000000000000000000000000 : ℝ)*base70 + (860579430701059/10000000000000000000000000000 : ℝ)*base72 + (1480642936818647/5000000000000000000000000000 : ℝ)*base75 + (2673113760818647/5000000000000000000000000000 : ℝ)*base76 + (160055928701059/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (13267/50000000000000000 : ℝ)*base87 + (13267/50000000000000000 : ℝ)*base89 + (63267/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(47573/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(47573/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18669436737917407025061/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3463033597/1250000000 : ℝ)*(base1) + (4444206421/3906250000 : ℝ)*(base7) + (1159900383369/1000000000000 : ℝ)*(base40) + (221684098711/500000000000 : ℝ)*(base50) + (179791606669/1000000000000 : ℝ)*(base60) + (681301324689/250000000000 : ℝ)*(major_s0_0) + (681301324689/250000000000 : ℝ)*(major_s0_1) + (681301324689/250000000000 : ℝ)*(major_s0_2) + (12878927/200000000000 : ℝ)*(sp_s0_1) + (527733/40000000000 : ℝ)*(sp_s0_2) + (1038349/25000000000 : ℝ)*(sp_s0_7) + (5911969940053/1000000000000 : ℝ)*(sp_s0_21) + (1570760100889/500000000000 : ℝ)*(sp_s0_22) + (196348212693/62500000000 : ℝ)*(sp_s0_23) + (51022188557/31250000000 : ℝ)*(f.failure) + (1570792298207/500000000000 : ℝ)*(f.sum) + (368714731801187/625000000000000000000000000 : ℝ)*base62 + (528297086194061/2500000000000000000000000000 : ℝ)*base65 + (344274225555939/2500000000000000000000000000 : ℝ)*base67 + (327591999363687/1250000000000000000000000000 : ℝ)*base68 + (174882011334287/500000000000000000000000000 : ℝ)*base71 + (1245474625805939/2500000000000000000000000000 : ℝ)*base73 + (406127773261313/1250000000000000000000000000 : ℝ)*base75 + (654246691511313/1250000000000000000000000000 : ℝ)*base76 + (278270272805939/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (2041/3125000000000000 : ℝ)*base87 + (2041/3125000000000000 : ℝ)*base89 + (2041/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (57893/100000 : ℝ) ^ (9/2 : ℝ) ≤ (8547069753401677009/100000000000000000000 : ℝ) := by
    have hpowers : (57893/100000 : ℝ)^9 ≤ (8547069753401677009/100000000000000000000 : ℝ)^2 := by
      have hnat : (57893 : ℕ)^9*100000000000000000000^2 ≤ 8547069753401677009^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57893 100000 8547069753401677009 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57893/100000 : ℝ)) (X := (8547069753401677009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (108547069753401677009/100000000000000000000 : ℝ) ≤ (10183923639196451/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (108547069753401677009/100000000000000000000 : ℝ)^2 ≤ (10183923639196451/10000000000000000 : ℝ)^9 := by
      have hnat : (108547069753401677009 : ℕ)^2*10000000000000000^9 ≤ 10183923639196451^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108547069753401677009 100000000000000000000 10183923639196451 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10183923639196451/10000000000000000 : ℝ)) (X := (108547069753401677009/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (58547069753401677009/50000000000000000000 : ℝ) ≤ (10356906020308153/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (58547069753401677009/50000000000000000000 : ℝ)^2 ≤ (10356906020308153/10000000000000000 : ℝ)^9 := by
      have hnat : (58547069753401677009 : ℕ)^2*10000000000000000^9 ≤ 10356906020308153^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58547069753401677009 50000000000000000000 10356906020308153 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10356906020308153/10000000000000000 : ℝ)) (X := (58547069753401677009/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16720330836041/526300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86491190555851/2894650000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (57893/100000 : ℝ)) (alpha := (16720330836041/526300000000000 : ℝ)) (beta := (86491190555851/2894650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (57893/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16720330836041/526300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86491190555851/2894650000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (73759/100000 : ℝ) ^ (9/2 : ℝ) ≤ (5083906866078602891/20000000000000000000 : ℝ) := by
    have hpowers : (73759/100000 : ℝ)^9 ≤ (5083906866078602891/20000000000000000000 : ℝ)^2 := by
      have hnat : (73759 : ℕ)^9*20000000000000000000^2 ≤ 5083906866078602891^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73759 100000 5083906866078602891 20000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73759/100000 : ℝ)) (X := (5083906866078602891/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25083906866078602891/20000000000000000000 : ℝ) ≤ (2629050561301537/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25083906866078602891/20000000000000000000 : ℝ)^2 ≤ (2629050561301537/2500000000000000 : ℝ)^9 := by
      have hnat : (25083906866078602891 : ℕ)^2*2500000000000000^9 ≤ 2629050561301537^9*20000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25083906866078602891 20000000000000000000 2629050561301537 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2629050561301537/2500000000000000 : ℝ)) (X := (25083906866078602891/20000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15083906866078602891/10000000000000000000 : ℝ) ≤ (10956447011973019/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (15083906866078602891/10000000000000000000 : ℝ)^2 ≤ (10956447011973019/10000000000000000 : ℝ)^9 := by
      have hnat : (15083906866078602891 : ℕ)^2*10000000000000000^9 ≤ 10956447011973019^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15083906866078602891 10000000000000000000 10956447011973019 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10956447011973019/10000000000000000 : ℝ)) (X := (15083906866078602891/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(129050561301537/1843975000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(440244766766871/7375900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (73759/100000 : ℝ)) (alpha := (129050561301537/1843975000000000 : ℝ)) (beta := (440244766766871/7375900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (73759/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(129050561301537/1843975000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(440244766766871/7375900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (47573/100000 : ℝ) ^ (9/2 : ℝ) ≤ (3532827456101736097/100000000000000000000 : ℝ) := by
    have hpowers : (47573/100000 : ℝ)^9 ≤ (3532827456101736097/100000000000000000000 : ℝ)^2 := by
      have hnat : (47573 : ℕ)^9*100000000000000000000^2 ≤ 3532827456101736097^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47573 100000 3532827456101736097 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47573/100000 : ℝ)) (X := (3532827456101736097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (103532827456101736097/100000000000000000000 : ℝ) ≤ (5038725362083509/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (103532827456101736097/100000000000000000000 : ℝ)^2 ≤ (5038725362083509/5000000000000000 : ℝ)^9 := by
      have hnat : (103532827456101736097 : ℕ)^2*5000000000000000^9 ≤ 5038725362083509^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103532827456101736097 100000000000000000000 5038725362083509 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038725362083509/5000000000000000 : ℝ)) (X := (103532827456101736097/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (53532827456101736097/50000000000000000000 : ℝ) ≤ (10152872408383717/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (53532827456101736097/50000000000000000000 : ℝ)^2 ≤ (10152872408383717/10000000000000000 : ℝ)^9 := by
      have hnat : (53532827456101736097 : ℕ)^2*10000000000000000^9 ≤ 10152872408383717^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53532827456101736097 50000000000000000000 10152872408383717 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10152872408383717/10000000000000000 : ℝ)) (X := (53532827456101736097/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(38725362083509/2378650000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(75421684216699/4757300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (47573/100000 : ℝ)) (alpha := (38725362083509/2378650000000000 : ℝ)) (beta := (75421684216699/4757300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (47573/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(38725362083509/2378650000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(75421684216699/4757300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4227076271/10000000000 : ℝ)*X 0 0+(-422707639/1000000000 : ℝ)*X 0 1+(4227076547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4227076271/10000000000 : ℝ)*X 1 0+(422707639/1000000000 : ℝ)*X 1 1+(4227076547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4227076271/10000000000 : ℝ)*X 2 0+(-422707639/1000000000 : ℝ)*X 2 1+(-4227076547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4227076271/10000000000 : ℝ)*X 0 0+(-422707639/1000000000 : ℝ)*X 0 1+(4227076547/10000000000 : ℝ)*X 0 2+(4227076271/10000000000 : ℝ)*X 1 0+(-422707639/1000000000 : ℝ)*X 1 1+(4227076547/10000000000 : ℝ)*X 1 2+(4227076271/10000000000 : ℝ)*X 2 0+(-422707639/1000000000 : ℝ)*X 2 1+(4227076547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312009_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-3184415214724489532273603599595453133/461688373538525000000000000000000000 : ℝ) := by norm_num
    linear_combination (12800761231/25000000000 : ℝ)*(base1) + (60858080331/250000000000 : ℝ)*(base3) + (108983/500000000000 : ℝ)*(base15) + (540883853593/1000000000000 : ℝ)*(base40) + (30997/500000000000 : ℝ)*(base43) + (119274368831/250000000000 : ℝ)*(base50) + (14975533373/250000000000 : ℝ)*(base59) + (115959140177/250000000000 : ℝ)*(base60) + (166913/100000 : ℝ)*(major_s1_0) + (834564969003/500000000000 : ℝ)*(major_s1_1) + (166913/100000 : ℝ)*(major_s1_2) + (175696190509/62500000000 : ℝ)*(sp_s1_0) + (79454398883/31250000000 : ℝ)*(sp_s1_1) + (459821719781/200000000000 : ℝ)*(sp_s1_2) + (244537229437/1000000000000 : ℝ)*(sp_s1_6) + (2299108660899/1000000000000 : ℝ)*(f.sum) + (103743202424763889983/175446845350000000000000000000000 : ℝ)*base63 + (7979969585593/47573000000000000000000000 : ℝ)*base64 + (26414003594407/57624218750000000000000000 : ℝ)*base67 + (207710861864881/475730000000000000000000000 : ℝ)*base69 + (1836342728727641/250376699000000000000000000000 : ℝ)*base71 + (136092840784403/578930000000000000000000000 : ℝ)*base72 + (215358073605683/1843975000000000000000000000 : ℝ)*base75 + (1021295741747/2631500000000000000000000 : ℝ)*base77 + (95841995556748544669/213506489350000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c312010_s0_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4227076403/10000000000 : ℝ)*x 0 + (-4227076403/10000000000 : ℝ)*x 1 + (-4227076403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ)] ![(6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312010_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076403/10000000000 : ℝ)*x 0 + (4227076403/10000000000 : ℝ)*x 1 + (-4227076403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076403/10000000000 : ℝ), (4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ)] ![(6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312010_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076403/10000000000 : ℝ)*x 0 + (-4227076403/10000000000 : ℝ)*x 1 + (4227076403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ), (4227076403/10000000000 : ℝ)] ![(6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312010_s0_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4227076403/10000000000 : ℝ)*x 0 + (-4227076403/10000000000 : ℝ)*x 1 + (-4227076403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227076403/10000000000 : ℝ)^37 ≤ (6666666666199/20000000000000 : ℝ)^29 := by
    have hnat : (4227076403 : ℕ)^37*20000000000000^29 ≤ 6666666666199^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227076403 10000000000 6666666666199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ), (-4227076403/10000000000 : ℝ)] ![(6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ), (6666666666199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4227076403/10000000000 : ℝ)|^37 ≤ (6666666666199/20000000000000 : ℝ)^29
        have hw : |(-4227076403/10000000000 : ℝ)|=(4227076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312010 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-4227076403/10000000000 : ℝ)*X 0 0+(-4227076403/10000000000 : ℝ)*X 0 1+(-4227076403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312010_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4227076403/10000000000 : ℝ)*X 1 0+(4227076403/10000000000 : ℝ)*X 1 1+(-4227076403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312010_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4227076403/10000000000 : ℝ)*X 2 0+(-4227076403/10000000000 : ℝ)*X 2 1+(4227076403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312010_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4227076403/10000000000 : ℝ)*X 0 0+(-4227076403/10000000000 : ℝ)*X 0 1+(-4227076403/10000000000 : ℝ)*X 0 2+(4227076403/10000000000 : ℝ)*X 1 0+(-4227076403/10000000000 : ℝ)*X 1 1+(-4227076403/10000000000 : ℝ)*X 1 2+(4227076403/10000000000 : ℝ)*X 2 0+(-4227076403/10000000000 : ℝ)*X 2 1+(-4227076403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312010_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-34486629548897845385063/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (12019096787/1000000000000 : ℝ)*(base6) + (11796591327/125000000000 : ℝ)*(base39) + (11796591327/125000000000 : ℝ)*(base49) + (11796591327/125000000000 : ℝ)*(base59) + (166913/100000 : ℝ)*(major_s0_0) + (166913/100000 : ℝ)*(major_s0_1) + (166913/100000 : ℝ)*(major_s0_2) + (2303115002187/1000000000000 : ℝ)*(sp_s0_0) + (2303115002187/1000000000000 : ℝ)*(sp_s0_1) + (2303115002187/1000000000000 : ℝ)*(sp_s0_2) + (987980903213/1000000000000 : ℝ)*(sp_s0_6) + (2303115002187/1000000000000 : ℝ)*(f.sum) + (4050319/5000000000000000000000 : ℝ)*base62 + (278125783/1000000000000000000000 : ℝ)*base65 + (278125783/1000000000000000000000 : ℝ)*base67 + (154764089/500000000000000000000 : ℝ)*base68 + (19120207/625000000000000000000 : ℝ)*base70 + (278125783/1000000000000000000000 : ℝ)*base73 + (154764089/500000000000000000000 : ℝ)*base74 + (154764089/500000000000000000000 : ℝ)*base77 + (309973631/5000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p012_b004 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 9 ≤ c.val) (hhi : c.val < 11)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=9 ∨ c=10 := by omega
  rcases hc with rfl|rfl
  · exact collision_c312009 p hpa (by linarith only [hpb]) X hX
  · exact collision_c312010 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 9 ≤ c.val) (hhi : c.val < 11)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b004 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
