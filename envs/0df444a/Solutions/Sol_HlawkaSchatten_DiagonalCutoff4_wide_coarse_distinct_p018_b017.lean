-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:33.416963+00:00
-- url     : https://prove2.me/submissions/2489b0d5-ac21-4351-87c0-b54334fce24a

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
theorem collision_support_c318037_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-213034461/2500000000 : ℝ)*x 0 + (-174890941/250000000 : ℝ)*x 1 + (3960380707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213034461/2500000000 : ℝ)^5 ≤ (4604021216443/100000000000000 : ℝ)^4 := by
    have hnat : (213034461 : ℕ)^5*100000000000000^4 ≤ 4604021216443^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213034461 2500000000 4604021216443 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174890941/250000000 : ℝ)^5 ≤ (63978511577209/100000000000000 : ℝ)^4 := by
    have hnat : (174890941 : ℕ)^5*100000000000000^4 ≤ 63978511577209^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174890941 250000000 63978511577209 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3960380707/10000000000 : ℝ)^5 ≤ (15708733595507/50000000000000 : ℝ)^4 := by
    have hnat : (3960380707 : ℕ)^5*50000000000000^4 ≤ 15708733595507^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3960380707 10000000000 15708733595507 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213034461/2500000000 : ℝ), (-174890941/250000000 : ℝ), (3960380707/10000000000 : ℝ)] ![(4604021216443/100000000000000 : ℝ), (63978511577209/100000000000000 : ℝ), (15708733595507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213034461/2500000000 : ℝ)|^5 ≤ (4604021216443/100000000000000 : ℝ)^4
        have hw : |(-213034461/2500000000 : ℝ)|=(213034461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174890941/250000000 : ℝ)|^5 ≤ (63978511577209/100000000000000 : ℝ)^4
        have hw : |(-174890941/250000000 : ℝ)|=(174890941/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3960380707/10000000000 : ℝ)|^5 ≤ (15708733595507/50000000000000 : ℝ)^4
        have hw : |(3960380707/10000000000 : ℝ)|=(3960380707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1234392367/2500000000 : ℝ)*x 0 + (-378171841/1250000000 : ℝ)*x 1 + (-4433090931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1234392367/2500000000 : ℝ)^5 ≤ (41389628049637/100000000000000 : ℝ)^4 := by
    have hnat : (1234392367 : ℕ)^5*100000000000000^4 ≤ 41389628049637^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234392367 2500000000 41389628049637 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378171841/1250000000 : ℝ)^5 ≤ (22437474298787/100000000000000 : ℝ)^4 := by
    have hnat : (378171841 : ℕ)^5*100000000000000^4 ≤ 22437474298787^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378171841 1250000000 22437474298787 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4433090931/10000000000 : ℝ)^5 ≤ (36172897643759/100000000000000 : ℝ)^4 := by
    have hnat : (4433090931 : ℕ)^5*100000000000000^4 ≤ 36172897643759^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433090931 10000000000 36172897643759 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1234392367/2500000000 : ℝ), (-378171841/1250000000 : ℝ), (-4433090931/10000000000 : ℝ)] ![(41389628049637/100000000000000 : ℝ), (22437474298787/100000000000000 : ℝ), (36172897643759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1234392367/2500000000 : ℝ)|^5 ≤ (41389628049637/100000000000000 : ℝ)^4
        have hw : |(1234392367/2500000000 : ℝ)|=(1234392367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378171841/1250000000 : ℝ)|^5 ≤ (22437474298787/100000000000000 : ℝ)^4
        have hw : |(-378171841/1250000000 : ℝ)|=(378171841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4433090931/10000000000 : ℝ)|^5 ≤ (36172897643759/100000000000000 : ℝ)^4
        have hw : |(-4433090931/10000000000 : ℝ)|=(4433090931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7851378221/10000000000 : ℝ)*x 0 + (-174046137/1250000000 : ℝ)*x 1 + (497974041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7851378221/10000000000 : ℝ)^5 ≤ (2309576730901/3125000000000 : ℝ)^4 := by
    have hnat : (7851378221 : ℕ)^5*3125000000000^4 ≤ 2309576730901^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7851378221 10000000000 2309576730901 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174046137/1250000000 : ℝ)^5 ≤ (8505365266289/100000000000000 : ℝ)^4 := by
    have hnat : (174046137 : ℕ)^5*100000000000000^4 ≤ 8505365266289^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174046137 1250000000 8505365266289 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497974041/2000000000 : ℝ)^5 ≤ (4397044835083/25000000000000 : ℝ)^4 := by
    have hnat : (497974041 : ℕ)^5*25000000000000^4 ≤ 4397044835083^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497974041 2000000000 4397044835083 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7851378221/10000000000 : ℝ), (-174046137/1250000000 : ℝ), (497974041/2000000000 : ℝ)] ![(2309576730901/3125000000000 : ℝ), (8505365266289/100000000000000 : ℝ), (4397044835083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7851378221/10000000000 : ℝ)|^5 ≤ (2309576730901/3125000000000 : ℝ)^4
        have hw : |(7851378221/10000000000 : ℝ)|=(7851378221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174046137/1250000000 : ℝ)|^5 ≤ (8505365266289/100000000000000 : ℝ)^4
        have hw : |(-174046137/1250000000 : ℝ)|=(174046137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497974041/2000000000 : ℝ)|^5 ≤ (4397044835083/25000000000000 : ℝ)^4
        have hw : |(497974041/2000000000 : ℝ)|=(497974041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-645455441/10000000000 : ℝ)*x 0 + (-8393593633/10000000000 : ℝ)*x 1 + (1177534061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (645455441/10000000000 : ℝ)^5 ≤ (1626682659123/50000000000000 : ℝ)^4 := by
    have hnat : (645455441 : ℕ)^5*50000000000000^4 ≤ 1626682659123^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645455441 10000000000 1626682659123 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8393593633/10000000000 : ℝ)^5 ≤ (80340572905329/100000000000000 : ℝ)^4 := by
    have hnat : (8393593633 : ℕ)^5*100000000000000^4 ≤ 80340572905329^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8393593633 10000000000 80340572905329 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1177534061/5000000000 : ℝ)^5 ≤ (8203030885597/50000000000000 : ℝ)^4 := by
    have hnat : (1177534061 : ℕ)^5*50000000000000^4 ≤ 8203030885597^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177534061 5000000000 8203030885597 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-645455441/10000000000 : ℝ), (-8393593633/10000000000 : ℝ), (1177534061/5000000000 : ℝ)] ![(1626682659123/50000000000000 : ℝ), (80340572905329/100000000000000 : ℝ), (8203030885597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-645455441/10000000000 : ℝ)|^5 ≤ (1626682659123/50000000000000 : ℝ)^4
        have hw : |(-645455441/10000000000 : ℝ)|=(645455441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8393593633/10000000000 : ℝ)|^5 ≤ (80340572905329/100000000000000 : ℝ)^4
        have hw : |(-8393593633/10000000000 : ℝ)|=(8393593633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1177534061/5000000000 : ℝ)|^5 ≤ (8203030885597/50000000000000 : ℝ)^4
        have hw : |(1177534061/5000000000 : ℝ)|=(1177534061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (296967047/625000000 : ℝ)*x 0 + (72541673/250000000 : ℝ)*x 1 + (591591063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (296967047/625000000 : ℝ)^5 ≤ (39448936886413/100000000000000 : ℝ)^4 := by
    have hnat : (296967047 : ℕ)^5*100000000000000^4 ≤ 39448936886413^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296967047 625000000 39448936886413 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72541673/250000000 : ℝ)^5 ≤ (21296559515359/100000000000000 : ℝ)^4 := by
    have hnat : (72541673 : ℕ)^5*100000000000000^4 ≤ 21296559515359^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72541673 250000000 21296559515359 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591591063/1250000000 : ℝ)^5 ≤ (39254503574871/100000000000000 : ℝ)^4 := by
    have hnat : (591591063 : ℕ)^5*100000000000000^4 ≤ 39254503574871^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591591063 1250000000 39254503574871 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(296967047/625000000 : ℝ), (72541673/250000000 : ℝ), (591591063/1250000000 : ℝ)] ![(39448936886413/100000000000000 : ℝ), (21296559515359/100000000000000 : ℝ), (39254503574871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(296967047/625000000 : ℝ)|^5 ≤ (39448936886413/100000000000000 : ℝ)^4
        have hw : |(296967047/625000000 : ℝ)|=(296967047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(72541673/250000000 : ℝ)|^5 ≤ (21296559515359/100000000000000 : ℝ)^4
        have hw : |(72541673/250000000 : ℝ)|=(72541673/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(591591063/1250000000 : ℝ)|^5 ≤ (39254503574871/100000000000000 : ℝ)^4
        have hw : |(591591063/1250000000 : ℝ)|=(591591063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (190059017/400000000 : ℝ)*x 0 + (-1181084179/5000000000 : ℝ)*x 1 + (-5192994699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190059017/400000000 : ℝ)^5 ≤ (39448964627027/100000000000000 : ℝ)^4 := by
    have hnat : (190059017 : ℕ)^5*100000000000000^4 ≤ 39448964627027^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190059017 400000000 39448964627027 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181084179/5000000000 : ℝ)^5 ≤ (329358256717/2000000000000 : ℝ)^4 := by
    have hnat : (1181084179 : ℕ)^5*2000000000000^4 ≤ 329358256717^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181084179 5000000000 329358256717 2000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192994699/10000000000 : ℝ)^5 ≤ (11020780629143/25000000000000 : ℝ)^4 := by
    have hnat : (5192994699 : ℕ)^5*25000000000000^4 ≤ 11020780629143^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192994699 10000000000 11020780629143 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(190059017/400000000 : ℝ), (-1181084179/5000000000 : ℝ), (-5192994699/10000000000 : ℝ)] ![(39448964627027/100000000000000 : ℝ), (329358256717/2000000000000 : ℝ), (11020780629143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(190059017/400000000 : ℝ)|^5 ≤ (39448964627027/100000000000000 : ℝ)^4
        have hw : |(190059017/400000000 : ℝ)|=(190059017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1181084179/5000000000 : ℝ)|^5 ≤ (329358256717/2000000000000 : ℝ)^4
        have hw : |(-1181084179/5000000000 : ℝ)|=(1181084179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5192994699/10000000000 : ℝ)|^5 ≤ (11020780629143/25000000000000 : ℝ)^4
        have hw : |(-5192994699/10000000000 : ℝ)|=(5192994699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3643078571/5000000000 : ℝ)*x 0 + (-61927729/2000000000 : ℝ)*x 1 + (989260567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3643078571/5000000000 : ℝ)^5 ≤ (538534032849/800000000000 : ℝ)^4 := by
    have hnat : (3643078571 : ℕ)^5*800000000000^4 ≤ 538534032849^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3643078571 5000000000 538534032849 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61927729/2000000000 : ℝ)^5 ≤ (162359969427/12500000000000 : ℝ)^4 := by
    have hnat : (61927729 : ℕ)^5*12500000000000^4 ≤ 162359969427^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61927729 2000000000 162359969427 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (989260567/2500000000 : ℝ)^5 ≤ (15692183064853/50000000000000 : ℝ)^4 := by
    have hnat : (989260567 : ℕ)^5*50000000000000^4 ≤ 15692183064853^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989260567 2500000000 15692183064853 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3643078571/5000000000 : ℝ), (-61927729/2000000000 : ℝ), (989260567/2500000000 : ℝ)] ![(538534032849/800000000000 : ℝ), (162359969427/12500000000000 : ℝ), (15692183064853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3643078571/5000000000 : ℝ)|^5 ≤ (538534032849/800000000000 : ℝ)^4
        have hw : |(3643078571/5000000000 : ℝ)|=(3643078571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61927729/2000000000 : ℝ)|^5 ≤ (162359969427/12500000000000 : ℝ)^4
        have hw : |(-61927729/2000000000 : ℝ)|=(61927729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(989260567/2500000000 : ℝ)|^5 ≤ (15692183064853/50000000000000 : ℝ)^4
        have hw : |(989260567/2500000000 : ℝ)|=(989260567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-37656753/5000000000 : ℝ)*x 0 + (-6751759033/10000000000 : ℝ)*x 1 + (93342173/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37656753/5000000000 : ℝ)^5 ≤ (110933083817/50000000000000 : ℝ)^4 := by
    have hnat : (37656753 : ℕ)^5*50000000000000^4 ≤ 110933083817^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37656753 5000000000 110933083817 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6751759033/10000000000 : ℝ)^5 ≤ (6120278256701/10000000000000 : ℝ)^4 := by
    have hnat : (6751759033 : ℕ)^5*10000000000000^4 ≤ 6120278256701^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6751759033 10000000000 6120278256701 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93342173/200000000 : ℝ)^5 ≤ (19287675622497/50000000000000 : ℝ)^4 := by
    have hnat : (93342173 : ℕ)^5*50000000000000^4 ≤ 19287675622497^4*200000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93342173 200000000 19287675622497 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37656753/5000000000 : ℝ), (-6751759033/10000000000 : ℝ), (93342173/200000000 : ℝ)] ![(110933083817/50000000000000 : ℝ), (6120278256701/10000000000000 : ℝ), (19287675622497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37656753/5000000000 : ℝ)|^5 ≤ (110933083817/50000000000000 : ℝ)^4
        have hw : |(-37656753/5000000000 : ℝ)|=(37656753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6751759033/10000000000 : ℝ)|^5 ≤ (6120278256701/10000000000000 : ℝ)^4
        have hw : |(-6751759033/10000000000 : ℝ)|=(6751759033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93342173/200000000 : ℝ)|^5 ≤ (19287675622497/50000000000000 : ℝ)^4
        have hw : |(93342173/200000000 : ℝ)|=(93342173/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4529476919/10000000000 : ℝ)*x 0 + (790436367/2500000000 : ℝ)*x 1 + (4720965993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4529476919/10000000000 : ℝ)^5 ≤ (37158661662491/100000000000000 : ℝ)^4 := by
    have hnat : (4529476919 : ℕ)^5*100000000000000^4 ≤ 37158661662491^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529476919 10000000000 37158661662491 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (790436367/2500000000 : ℝ)^5 ≤ (23708748563749/100000000000000 : ℝ)^4 := by
    have hnat : (790436367 : ℕ)^5*100000000000000^4 ≤ 23708748563749^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790436367 2500000000 23708748563749 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4720965993/10000000000 : ℝ)^5 ≤ (39132589758499/100000000000000 : ℝ)^4 := by
    have hnat : (4720965993 : ℕ)^5*100000000000000^4 ≤ 39132589758499^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4720965993 10000000000 39132589758499 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4529476919/10000000000 : ℝ), (790436367/2500000000 : ℝ), (4720965993/10000000000 : ℝ)] ![(37158661662491/100000000000000 : ℝ), (23708748563749/100000000000000 : ℝ), (39132589758499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4529476919/10000000000 : ℝ)|^5 ≤ (37158661662491/100000000000000 : ℝ)^4
        have hw : |(4529476919/10000000000 : ℝ)|=(4529476919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(790436367/2500000000 : ℝ)|^5 ≤ (23708748563749/100000000000000 : ℝ)^4
        have hw : |(790436367/2500000000 : ℝ)|=(790436367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4720965993/10000000000 : ℝ)|^5 ≤ (39132589758499/100000000000000 : ℝ)^4
        have hw : |(4720965993/10000000000 : ℝ)|=(4720965993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (575955783/1000000000 : ℝ)*x 0 + (-2579570357/10000000000 : ℝ)*x 1 + (-3962789503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (575955783/1000000000 : ℝ)^5 ≤ (25087445001571/50000000000000 : ℝ)^4 := by
    have hnat : (575955783 : ℕ)^5*50000000000000^4 ≤ 25087445001571^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575955783 1000000000 25087445001571 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579570357/10000000000 : ℝ)^5 ≤ (18383754935627/100000000000000 : ℝ)^4 := by
    have hnat : (2579570357 : ℕ)^5*100000000000000^4 ≤ 18383754935627^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579570357 10000000000 18383754935627 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3962789503/10000000000 : ℝ)^5 ≤ (15720677526483/50000000000000 : ℝ)^4 := by
    have hnat : (3962789503 : ℕ)^5*50000000000000^4 ≤ 15720677526483^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3962789503 10000000000 15720677526483 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(575955783/1000000000 : ℝ), (-2579570357/10000000000 : ℝ), (-3962789503/10000000000 : ℝ)] ![(25087445001571/50000000000000 : ℝ), (18383754935627/100000000000000 : ℝ), (15720677526483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(575955783/1000000000 : ℝ)|^5 ≤ (25087445001571/50000000000000 : ℝ)^4
        have hw : |(575955783/1000000000 : ℝ)|=(575955783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2579570357/10000000000 : ℝ)|^5 ≤ (18383754935627/100000000000000 : ℝ)^4
        have hw : |(-2579570357/10000000000 : ℝ)|=(2579570357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3962789503/10000000000 : ℝ)|^5 ≤ (15720677526483/50000000000000 : ℝ)^4
        have hw : |(-3962789503/10000000000 : ℝ)|=(3962789503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4517332333/5000000000 : ℝ)*x 0 + (-971613247/10000000000 : ℝ)*x 1 + (1121881781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4517332333/5000000000 : ℝ)^5 ≤ (44041292054733/50000000000000 : ℝ)^4 := by
    have hnat : (4517332333 : ℕ)^5*50000000000000^4 ≤ 44041292054733^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517332333 5000000000 44041292054733 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971613247/10000000000 : ℝ)^5 ≤ (678073539487/12500000000000 : ℝ)^4 := by
    have hnat : (971613247 : ℕ)^5*12500000000000^4 ≤ 678073539487^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971613247 10000000000 678073539487 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121881781/10000000000 : ℝ)^5 ≤ (3246413782209/50000000000000 : ℝ)^4 := by
    have hnat : (1121881781 : ℕ)^5*50000000000000^4 ≤ 3246413782209^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121881781 10000000000 3246413782209 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4517332333/5000000000 : ℝ), (-971613247/10000000000 : ℝ), (1121881781/10000000000 : ℝ)] ![(44041292054733/50000000000000 : ℝ), (678073539487/12500000000000 : ℝ), (3246413782209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4517332333/5000000000 : ℝ)|^5 ≤ (44041292054733/50000000000000 : ℝ)^4
        have hw : |(4517332333/5000000000 : ℝ)|=(4517332333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971613247/10000000000 : ℝ)|^5 ≤ (678073539487/12500000000000 : ℝ)^4
        have hw : |(-971613247/10000000000 : ℝ)|=(971613247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121881781/10000000000 : ℝ)|^5 ≤ (3246413782209/50000000000000 : ℝ)^4
        have hw : |(1121881781/10000000000 : ℝ)|=(1121881781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-53783887/5000000000 : ℝ)*x 0 + (-7765225601/10000000000 : ℝ)*x 1 + (3483226061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53783887/5000000000 : ℝ)^5 ≤ (34641981611/10000000000000 : ℝ)^4 := by
    have hnat : (53783887 : ℕ)^5*10000000000000^4 ≤ 34641981611^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53783887 5000000000 34641981611 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7765225601/10000000000 : ℝ)^5 ≤ (36447068368633/50000000000000 : ℝ)^4 := by
    have hnat : (7765225601 : ℕ)^5*50000000000000^4 ≤ 36447068368633^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7765225601 10000000000 36447068368633 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3483226061/10000000000 : ℝ)^5 ≤ (26759443430293/100000000000000 : ℝ)^4 := by
    have hnat : (3483226061 : ℕ)^5*100000000000000^4 ≤ 26759443430293^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3483226061 10000000000 26759443430293 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53783887/5000000000 : ℝ), (-7765225601/10000000000 : ℝ), (3483226061/10000000000 : ℝ)] ![(34641981611/10000000000000 : ℝ), (36447068368633/50000000000000 : ℝ), (26759443430293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53783887/5000000000 : ℝ)|^5 ≤ (34641981611/10000000000000 : ℝ)^4
        have hw : |(-53783887/5000000000 : ℝ)|=(53783887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7765225601/10000000000 : ℝ)|^5 ≤ (36447068368633/50000000000000 : ℝ)^4
        have hw : |(-7765225601/10000000000 : ℝ)|=(7765225601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3483226061/10000000000 : ℝ)|^5 ≤ (26759443430293/100000000000000 : ℝ)^4
        have hw : |(3483226061/10000000000 : ℝ)|=(3483226061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5727301617/10000000000 : ℝ)*x 0 + (693389409/2500000000 : ℝ)*x 1 + (382169501/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5727301617/10000000000 : ℝ)^5 ≤ (24911941366367/50000000000000 : ℝ)^4 := by
    have hnat : (5727301617 : ℕ)^5*50000000000000^4 ≤ 24911941366367^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5727301617 10000000000 24911941366367 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693389409/2500000000 : ℝ)^5 ≤ (20127808599781/100000000000000 : ℝ)^4 := by
    have hnat : (693389409 : ℕ)^5*100000000000000^4 ≤ 20127808599781^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693389409 2500000000 20127808599781 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382169501/1000000000 : ℝ)^5 ≤ (6009661729989/20000000000000 : ℝ)^4 := by
    have hnat : (382169501 : ℕ)^5*20000000000000^4 ≤ 6009661729989^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382169501 1000000000 6009661729989 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5727301617/10000000000 : ℝ), (693389409/2500000000 : ℝ), (382169501/1000000000 : ℝ)] ![(24911941366367/50000000000000 : ℝ), (20127808599781/100000000000000 : ℝ), (6009661729989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5727301617/10000000000 : ℝ)|^5 ≤ (24911941366367/50000000000000 : ℝ)^4
        have hw : |(5727301617/10000000000 : ℝ)|=(5727301617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(693389409/2500000000 : ℝ)|^5 ≤ (20127808599781/100000000000000 : ℝ)^4
        have hw : |(693389409/2500000000 : ℝ)|=(693389409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(382169501/1000000000 : ℝ)|^5 ≤ (6009661729989/20000000000000 : ℝ)^4
        have hw : |(382169501/1000000000 : ℝ)|=(382169501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4526683389/10000000000 : ℝ)*x 0 + (-1552701863/5000000000 : ℝ)*x 1 + (-4774509589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4526683389/10000000000 : ℝ)^5 ≤ (37130017120809/100000000000000 : ℝ)^4 := by
    have hnat : (4526683389 : ℕ)^5*100000000000000^4 ≤ 37130017120809^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526683389 10000000000 37130017120809 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552701863/5000000000 : ℝ)^5 ≤ (11590911544097/50000000000000 : ℝ)^4 := by
    have hnat : (1552701863 : ℕ)^5*50000000000000^4 ≤ 11590911544097^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552701863 5000000000 11590911544097 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774509589/10000000000 : ℝ)^5 ≤ (9922039943341/25000000000000 : ℝ)^4 := by
    have hnat : (4774509589 : ℕ)^5*25000000000000^4 ≤ 9922039943341^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774509589 10000000000 9922039943341 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4526683389/10000000000 : ℝ), (-1552701863/5000000000 : ℝ), (-4774509589/10000000000 : ℝ)] ![(37130017120809/100000000000000 : ℝ), (11590911544097/50000000000000 : ℝ), (9922039943341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4526683389/10000000000 : ℝ)|^5 ≤ (37130017120809/100000000000000 : ℝ)^4
        have hw : |(4526683389/10000000000 : ℝ)|=(4526683389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1552701863/5000000000 : ℝ)|^5 ≤ (11590911544097/50000000000000 : ℝ)^4
        have hw : |(-1552701863/5000000000 : ℝ)|=(1552701863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4774509589/10000000000 : ℝ)|^5 ≤ (9922039943341/25000000000000 : ℝ)^4
        have hw : |(-4774509589/10000000000 : ℝ)|=(4774509589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s0_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4521032867/5000000000 : ℝ)*x 0 + (-17236349/500000000 : ℝ)*x 1 + (1628085551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4521032867/5000000000 : ℝ)^5 ≤ (8817278833383/10000000000000 : ℝ)^4 := by
    have hnat : (4521032867 : ℕ)^5*10000000000000^4 ≤ 8817278833383^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521032867 5000000000 8817278833383 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17236349/500000000 : ℝ)^5 ≤ (74270115233/5000000000000 : ℝ)^4 := by
    have hnat : (17236349 : ℕ)^5*5000000000000^4 ≤ 74270115233^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17236349 500000000 74270115233 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1628085551/10000000000 : ℝ)^5 ≤ (10341809354371/100000000000000 : ℝ)^4 := by
    have hnat : (1628085551 : ℕ)^5*100000000000000^4 ≤ 10341809354371^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628085551 10000000000 10341809354371 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4521032867/5000000000 : ℝ), (-17236349/500000000 : ℝ), (1628085551/10000000000 : ℝ)] ![(8817278833383/10000000000000 : ℝ), (74270115233/5000000000000 : ℝ), (10341809354371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4521032867/5000000000 : ℝ)|^5 ≤ (8817278833383/10000000000000 : ℝ)^4
        have hw : |(4521032867/5000000000 : ℝ)|=(4521032867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17236349/500000000 : ℝ)|^5 ≤ (74270115233/5000000000000 : ℝ)^4
        have hw : |(-17236349/500000000 : ℝ)|=(17236349/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1628085551/10000000000 : ℝ)|^5 ≤ (10341809354371/100000000000000 : ℝ)^4
        have hw : |(1628085551/10000000000 : ℝ)|=(1628085551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-438061461/2000000000 : ℝ)*x 0 + (-5674863213/10000000000 : ℝ)*x 1 + (4392717039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438061461/2000000000 : ℝ)^5 ≤ (936507655433/6250000000000 : ℝ)^4 := by
    have hnat : (438061461 : ℕ)^5*6250000000000^4 ≤ 936507655433^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438061461 2000000000 936507655433 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674863213/10000000000 : ℝ)^5 ≤ (12313577719393/25000000000000 : ℝ)^4 := by
    have hnat : (5674863213 : ℕ)^5*25000000000000^4 ≤ 12313577719393^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674863213 10000000000 12313577719393 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4392717039/10000000000 : ℝ)^5 ≤ (35761566620903/100000000000000 : ℝ)^4 := by
    have hnat : (4392717039 : ℕ)^5*100000000000000^4 ≤ 35761566620903^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392717039 10000000000 35761566620903 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438061461/2000000000 : ℝ), (-5674863213/10000000000 : ℝ), (4392717039/10000000000 : ℝ)] ![(936507655433/6250000000000 : ℝ), (12313577719393/25000000000000 : ℝ), (35761566620903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438061461/2000000000 : ℝ)|^5 ≤ (936507655433/6250000000000 : ℝ)^4
        have hw : |(-438061461/2000000000 : ℝ)|=(438061461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5674863213/10000000000 : ℝ)|^5 ≤ (12313577719393/25000000000000 : ℝ)^4
        have hw : |(-5674863213/10000000000 : ℝ)|=(5674863213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4392717039/10000000000 : ℝ)|^5 ≤ (35761566620903/100000000000000 : ℝ)^4
        have hw : |(4392717039/10000000000 : ℝ)|=(4392717039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (593515941/1250000000 : ℝ)*x 0 + (1722566761/5000000000 : ℝ)*x 1 + (4237755347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (593515941/1250000000 : ℝ)^5 ≤ (39414222935163/100000000000000 : ℝ)^4 := by
    have hnat : (593515941 : ℕ)^5*100000000000000^4 ≤ 39414222935163^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593515941 1250000000 39414222935163 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722566761/5000000000 : ℝ)^5 ≤ (527882869323/2000000000000 : ℝ)^4 := by
    have hnat : (1722566761 : ℕ)^5*2000000000000^4 ≤ 527882869323^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722566761 5000000000 527882869323 2000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237755347/10000000000 : ℝ)^5 ≤ (34191633579341/100000000000000 : ℝ)^4 := by
    have hnat : (4237755347 : ℕ)^5*100000000000000^4 ≤ 34191633579341^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237755347 10000000000 34191633579341 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(593515941/1250000000 : ℝ), (1722566761/5000000000 : ℝ), (4237755347/10000000000 : ℝ)] ![(39414222935163/100000000000000 : ℝ), (527882869323/2000000000000 : ℝ), (34191633579341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(593515941/1250000000 : ℝ)|^5 ≤ (39414222935163/100000000000000 : ℝ)^4
        have hw : |(593515941/1250000000 : ℝ)|=(593515941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1722566761/5000000000 : ℝ)|^5 ≤ (527882869323/2000000000000 : ℝ)^4
        have hw : |(1722566761/5000000000 : ℝ)|=(1722566761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237755347/10000000000 : ℝ)|^5 ≤ (34191633579341/100000000000000 : ℝ)^4
        have hw : |(4237755347/10000000000 : ℝ)|=(4237755347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (235735143/500000000 : ℝ)*x 0 + (-1730443967/5000000000 : ℝ)*x 1 + (-1362283/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235735143/500000000 : ℝ)^5 ≤ (39067705803409/100000000000000 : ℝ)^4 := by
    have hnat : (235735143 : ℕ)^5*100000000000000^4 ≤ 39067705803409^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235735143 500000000 39067705803409 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730443967/5000000000 : ℝ)^5 ≤ (26545103374323/100000000000000 : ℝ)^4 := by
    have hnat : (1730443967 : ℕ)^5*100000000000000^4 ≤ 26545103374323^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730443967 5000000000 26545103374323 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362283/3200000 : ℝ)^5 ≤ (8596797701549/25000000000000 : ℝ)^4 := by
    have hnat : (1362283 : ℕ)^5*25000000000000^4 ≤ 8596797701549^4*3200000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362283 3200000 8596797701549 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(235735143/500000000 : ℝ), (-1730443967/5000000000 : ℝ), (-1362283/3200000 : ℝ)] ![(39067705803409/100000000000000 : ℝ), (26545103374323/100000000000000 : ℝ), (8596797701549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(235735143/500000000 : ℝ)|^5 ≤ (39067705803409/100000000000000 : ℝ)^4
        have hw : |(235735143/500000000 : ℝ)|=(235735143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1730443967/5000000000 : ℝ)|^5 ≤ (26545103374323/100000000000000 : ℝ)^4
        have hw : |(-1730443967/5000000000 : ℝ)|=(1730443967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1362283/3200000 : ℝ)|^5 ≤ (8596797701549/25000000000000 : ℝ)^4
        have hw : |(-1362283/3200000 : ℝ)|=(1362283/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318037_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5983640957/10000000000 : ℝ)*x 0 + (-1777262573/5000000000 : ℝ)*x 1 + (1375718021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5983640957/10000000000 : ℝ)^5 ≤ (13156698316151/25000000000000 : ℝ)^4 := by
    have hnat : (5983640957 : ℕ)^5*25000000000000^4 ≤ 13156698316151^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5983640957 10000000000 13156698316151 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1777262573/5000000000 : ℝ)^5 ≤ (27445869161579/100000000000000 : ℝ)^4 := by
    have hnat : (1777262573 : ℕ)^5*100000000000000^4 ≤ 27445869161579^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777262573 5000000000 27445869161579 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375718021/5000000000 : ℝ)^5 ≤ (2490917193999/12500000000000 : ℝ)^4 := by
    have hnat : (1375718021 : ℕ)^5*12500000000000^4 ≤ 2490917193999^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375718021 5000000000 2490917193999 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5983640957/10000000000 : ℝ), (-1777262573/5000000000 : ℝ), (1375718021/5000000000 : ℝ)] ![(13156698316151/25000000000000 : ℝ), (27445869161579/100000000000000 : ℝ), (2490917193999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5983640957/10000000000 : ℝ)|^5 ≤ (13156698316151/25000000000000 : ℝ)^4
        have hw : |(5983640957/10000000000 : ℝ)|=(5983640957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1777262573/5000000000 : ℝ)|^5 ≤ (27445869161579/100000000000000 : ℝ)^4
        have hw : |(-1777262573/5000000000 : ℝ)|=(1777262573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375718021/5000000000 : ℝ)|^5 ≤ (2490917193999/12500000000000 : ℝ)^4
        have hw : |(1375718021/5000000000 : ℝ)|=(1375718021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318037 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-213034461/2500000000 : ℝ)*X 0 0+(-174890941/250000000 : ℝ)*X 0 1+(3960380707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1234392367/2500000000 : ℝ)*X 2 0+(-378171841/1250000000 : ℝ)*X 2 1+(-4433090931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7851378221/10000000000 : ℝ)*X 0 0+(-174046137/1250000000 : ℝ)*X 0 1+(497974041/2000000000 : ℝ)*X 0 2+(7851378221/10000000000 : ℝ)*X 1 0+(-174046137/1250000000 : ℝ)*X 1 1+(497974041/2000000000 : ℝ)*X 1 2+(7851378221/10000000000 : ℝ)*X 2 0+(-174046137/1250000000 : ℝ)*X 2 1+(497974041/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-645455441/10000000000 : ℝ)*X 0 0+(-8393593633/10000000000 : ℝ)*X 0 1+(1177534061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((296967047/625000000 : ℝ)*X 1 0+(72541673/250000000 : ℝ)*X 1 1+(591591063/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((190059017/400000000 : ℝ)*X 2 0+(-1181084179/5000000000 : ℝ)*X 2 1+(-5192994699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3643078571/5000000000 : ℝ)*X 0 0+(-61927729/2000000000 : ℝ)*X 0 1+(989260567/2500000000 : ℝ)*X 0 2+(3643078571/5000000000 : ℝ)*X 1 0+(-61927729/2000000000 : ℝ)*X 1 1+(989260567/2500000000 : ℝ)*X 1 2+(3643078571/5000000000 : ℝ)*X 2 0+(-61927729/2000000000 : ℝ)*X 2 1+(989260567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-37656753/5000000000 : ℝ)*X 0 0+(-6751759033/10000000000 : ℝ)*X 0 1+(93342173/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4529476919/10000000000 : ℝ)*X 1 0+(790436367/2500000000 : ℝ)*X 1 1+(4720965993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((575955783/1000000000 : ℝ)*X 2 0+(-2579570357/10000000000 : ℝ)*X 2 1+(-3962789503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4517332333/5000000000 : ℝ)*X 0 0+(-971613247/10000000000 : ℝ)*X 0 1+(1121881781/10000000000 : ℝ)*X 0 2+(4517332333/5000000000 : ℝ)*X 1 0+(-971613247/10000000000 : ℝ)*X 1 1+(1121881781/10000000000 : ℝ)*X 1 2+(4517332333/5000000000 : ℝ)*X 2 0+(-971613247/10000000000 : ℝ)*X 2 1+(1121881781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-53783887/5000000000 : ℝ)*X 0 0+(-7765225601/10000000000 : ℝ)*X 0 1+(3483226061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5727301617/10000000000 : ℝ)*X 1 0+(693389409/2500000000 : ℝ)*X 1 1+(382169501/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4526683389/10000000000 : ℝ)*X 2 0+(-1552701863/5000000000 : ℝ)*X 2 1+(-4774509589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4521032867/5000000000 : ℝ)*X 0 0+(-17236349/500000000 : ℝ)*X 0 1+(1628085551/10000000000 : ℝ)*X 0 2+(4521032867/5000000000 : ℝ)*X 1 0+(-17236349/500000000 : ℝ)*X 1 1+(1628085551/10000000000 : ℝ)*X 1 2+(4521032867/5000000000 : ℝ)*X 2 0+(-17236349/500000000 : ℝ)*X 2 1+(1628085551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21829/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21829/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (425098838397955319877/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1381317/200000000000 : ℝ)*(base3) + (134524560969/200000000000 : ℝ)*(base40) + (1171287689693/1000000000000 : ℝ)*(base49) + (232941103127/500000000000 : ℝ)*(base59) + (343272160283/100000000000 : ℝ)*(major_s0_0) + (343272160283/100000000000 : ℝ)*(major_s0_1) + (343272160283/100000000000 : ℝ)*(major_s0_2) + (2492068309221/500000000000 : ℝ)*(sp_s0_7) + (4984049029061/1000000000000 : ℝ)*(sp_s0_8) + (311508203663/62500000000 : ℝ)*(sp_s0_9) + (470298534051/250000000000 : ℝ)*(sp_s0_13) + (194372403/1000000000000 : ℝ)*(sp_s0_15) + (24969109/250000000000 : ℝ)*(sp_s0_21) + (105236271/1000000000000 : ℝ)*(sp_s0_23) + (1881201042789/1000000000000 : ℝ)*(f.failure) + (4984236494879/1000000000000 : ℝ)*(f.sum) + (2771086275497/250000000000000000000000000 : ℝ)*base62 + (462712661224913/500000000000000000000000000 : ℝ)*base64 + (327237509075087/500000000000000000000000000 : ℝ)*base67 + (125373668424503/500000000000000000000000000 : ℝ)*base69 + (1859991025041/50000000000000000000000000 : ℝ)*base70 + (102742901574913/500000000000000000000000000 : ℝ)*base73 + (44823738924503/500000000000000000000000000 : ℝ)*base75 + (48098522225497/500000000000000000000000000 : ℝ)*base76 + (3565150939/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (3089/4000000000000000 : ℝ)*base86 + (3089/4000000000000000 : ℝ)*base88 + (3089/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37173/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-37173/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (333398150037148518849/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1669847/1000000000000 : ℝ)*(base39) + (988282506317/500000000000 : ℝ)*(base40) + (450388712359/500000000000 : ℝ)*(base49) + (1399737857179/250000000000 : ℝ)*(major_s0_0) + (1399737857179/250000000000 : ℝ)*(major_s0_1) + (1399737857179/250000000000 : ℝ)*(major_s0_2) + (3335587/500000000000 : ℝ)*(sp_s0_6) + (64888879/1000000000000 : ℝ)*(sp_s0_8) + (4793631/1000000000000 : ℝ)*(sp_s0_9) + (812956216783/100000000000 : ℝ)*(sp_s0_14) + (8129497278951/1000000000000 : ℝ)*(sp_s0_15) + (8129557374199/1000000000000 : ℝ)*(sp_s0_16) + (3068294318909/1000000000000 : ℝ)*(sp_s0_20) + (37921393/1000000000000 : ℝ)*(sp_s0_27) + (767084727869/250000000000 : ℝ)*(f.failure) + (812956216783/100000000000 : ℝ)*(f.sum) + (119453475707039/625000000000000000000000000 : ℝ)*base63 + (351789386792631/1250000000000000000000000000 : ℝ)*base65 + (52849038082369/1250000000000000000000000000 : ℝ)*base66 + (72380539542961/1250000000000000000000000000 : ℝ)*base68 + (26760136587467/125000000000000000000000000 : ℝ)*base71 + (133684729792631/1250000000000000000000000000 : ℝ)*base72 + (28391710542961/1250000000000000000000000000 : ℝ)*base74 + (563410909832039/1250000000000000000000000000 : ℝ)*base77 + (200577189/625000000000000000000 : ℝ)*base79 + (169/1000000000000000 : ℝ)*base86 + (169/1000000000000000 : ℝ)*base88 + (169/1000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44993/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (99281899934773766199/15625000000000000000000000 : ℝ) := by norm_num
    linear_combination (541253941691/250000000000 : ℝ)*(base40) + (1299887960301/1000000000000 : ℝ)*(base49) + (13310230889/50000000000 : ℝ)*(base59) + (286817109107/50000000000 : ℝ)*(major_s0_0) + (286817109107/50000000000 : ℝ)*(major_s0_1) + (286817109107/50000000000 : ℝ)*(major_s0_2) + (1543791/500000000000 : ℝ)*(sp_s0_0) + (4746553/200000000000 : ℝ)*(sp_s0_2) + (19853173/1000000000000 : ℝ)*(sp_s0_7) + (391519/12500000000 : ℝ)*(sp_s0_20) + (8329027475313/1000000000000 : ℝ)*(sp_s0_21) + (2082262604017/250000000000 : ℝ)*(sp_s0_22) + (8329026683303/1000000000000 : ℝ)*(sp_s0_23) + (3143600508671/1000000000000 : ℝ)*(sp_s0_27) + (314363183019/100000000000 : ℝ)*(f.failure) + (2082262604017/250000000000 : ℝ)*(f.sum) + (67300795860013/125000000000000000000000000 : ℝ)*base62 + (20402167582377/250000000000000000000000000 : ℝ)*base64 + (102809216517623/250000000000000000000000000 : ℝ)*base67 + (53160002222513/250000000000000000000000000 : ℝ)*base68 + (20650174119511/25000000000000000000000000 : ℝ)*base71 + (55438317392623/250000000000000000000000000 : ℝ)*base72 + (66404775497513/250000000000000000000000000 : ℝ)*base74 + (52043565477487/250000000000000000000000000 : ℝ)*base77 + (3817793159/10000000000000000000000 : ℝ)*base78 + (319/400000000000000 : ℝ)*base86 + (319/400000000000000 : ℝ)*base88 + (319/400000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (21829/100000 : ℝ) ^ (39/8 : ℝ) ≤ (1873440894000869/3125000000000000000 : ℝ) := by
    have hpowers : (21829/100000 : ℝ)^39 ≤ (1873440894000869/3125000000000000000 : ℝ)^8 := by
      have hnat : (21829 : ℕ)^39*3125000000000000000^8 ≤ 1873440894000869^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21829 100000 1873440894000869 3125000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21829/100000 : ℝ)) (X := (1873440894000869/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3126873440894000869/3125000000000000000 : ℝ) ≤ (2500307363229853/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3126873440894000869/3125000000000000000 : ℝ)^8 ≤ (2500307363229853/2500000000000000 : ℝ)^39 := by
      have hnat : (3126873440894000869 : ℕ)^8*2500000000000000^39 ≤ 2500307363229853^39*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126873440894000869 3125000000000000000 2500307363229853 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500307363229853/2500000000000000 : ℝ)) (X := (3126873440894000869/3125000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1564373440894000869/1562500000000000000 : ℝ) ≤ (2500614580115573/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (1564373440894000869/1562500000000000000 : ℝ)^8 ≤ (2500614580115573/2500000000000000 : ℝ)^39 := by
      have hnat : (1564373440894000869 : ℕ)^8*2500000000000000^39 ≤ 2500614580115573^39*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564373440894000869 1562500000000000000 2500614580115573 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500614580115573/2500000000000000 : ℝ)) (X := (1564373440894000869/1562500000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(307363229853/545725000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7680422143/13643125000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (21829/100000 : ℝ)) (alpha := (307363229853/545725000000000 : ℝ)) (beta := (7680422143/13643125000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21829/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(307363229853/545725000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7680422143/13643125000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (37173/100000 : ℝ) ^ (39/8 : ℝ) ≤ (803266410871848333/100000000000000000000 : ℝ) := by
    have hpowers : (37173/100000 : ℝ)^39 ≤ (803266410871848333/100000000000000000000 : ℝ)^8 := by
      have hnat : (37173 : ℕ)^39*100000000000000000000^8 ≤ 803266410871848333^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37173 100000 803266410871848333 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37173/100000 : ℝ)) (X := (803266410871848333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100803266410871848333/100000000000000000000 : ℝ) ≤ (10016424907961671/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (100803266410871848333/100000000000000000000 : ℝ)^8 ≤ (10016424907961671/10000000000000000 : ℝ)^39 := by
      have hnat : (100803266410871848333 : ℕ)^8*10000000000000000^39 ≤ 10016424907961671^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100803266410871848333 100000000000000000000 10016424907961671 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016424907961671/10000000000000000 : ℝ)) (X := (100803266410871848333/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50803266410871848333/50000000000000000000 : ℝ) ≤ (10032746106853593/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50803266410871848333/50000000000000000000 : ℝ)^8 ≤ (10032746106853593/10000000000000000 : ℝ)^39 := by
      have hnat : (50803266410871848333 : ℕ)^8*10000000000000000^39 ≤ 10032746106853593^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50803266410871848333 50000000000000000000 10032746106853593 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032746106853593/10000000000000000 : ℝ)) (X := (50803266410871848333/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5474969320557/1239100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8160599445961/1858650000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (37173/100000 : ℝ)) (alpha := (5474969320557/1239100000000000 : ℝ)) (beta := (8160599445961/1858650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (37173/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5474969320557/1239100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8160599445961/1858650000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (44993/100000 : ℝ) ^ (39/8 : ℝ) ≤ (2037425038641987791/100000000000000000000 : ℝ) := by
    have hpowers : (44993/100000 : ℝ)^39 ≤ (2037425038641987791/100000000000000000000 : ℝ)^8 := by
      have hnat : (44993 : ℕ)^39*100000000000000000000^8 ≤ 2037425038641987791^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44993 100000 2037425038641987791 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44993/100000 : ℝ)) (X := (2037425038641987791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102037425038641987791/100000000000000000000 : ℝ) ≤ (5020729490874189/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (102037425038641987791/100000000000000000000 : ℝ)^8 ≤ (5020729490874189/5000000000000000 : ℝ)^39 := by
      have hnat : (102037425038641987791 : ℕ)^8*5000000000000000^39 ≤ 5020729490874189^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102037425038641987791 100000000000000000000 5020729490874189 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020729490874189/5000000000000000 : ℝ)) (X := (102037425038641987791/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52037425038641987791/50000000000000000000 : ℝ) ≤ (2520566269892083/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (52037425038641987791/50000000000000000000 : ℝ)^8 ≤ (2520566269892083/2500000000000000 : ℝ)^39 := by
      have hnat : (52037425038641987791 : ℕ)^8*2500000000000000^39 ≤ 2520566269892083^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52037425038641987791 50000000000000000000 2520566269892083 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2520566269892083/2500000000000000 : ℝ)) (X := (52037425038641987791/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(20729490874189/2249650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(20403048909977/2249650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (44993/100000 : ℝ)) (alpha := (20729490874189/2249650000000000 : ℝ)) (beta := (20403048909977/2249650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44993/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(20729490874189/2249650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(20403048909977/2249650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-438061461/2000000000 : ℝ)*X 0 0+(-5674863213/10000000000 : ℝ)*X 0 1+(4392717039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((593515941/1250000000 : ℝ)*X 1 0+(1722566761/5000000000 : ℝ)*X 1 1+(4237755347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((235735143/500000000 : ℝ)*X 2 0+(-1730443967/5000000000 : ℝ)*X 2 1+(-1362283/3200000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5983640957/10000000000 : ℝ)*X 0 0+(-1777262573/5000000000 : ℝ)*X 0 1+(1375718021/5000000000 : ℝ)*X 0 2+(5983640957/10000000000 : ℝ)*X 1 0+(-1777262573/5000000000 : ℝ)*X 1 1+(1375718021/5000000000 : ℝ)*X 1 2+(5983640957/10000000000 : ℝ)*X 2 0+(-1777262573/5000000000 : ℝ)*X 2 1+(1375718021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-1194909714568396151739054762229259433/152123098412837500000000000000000000 : ℝ) := by norm_num
    linear_combination (129/125000000000 : ℝ)*(base3) + (153/100000000000 : ℝ)*(base13) + (60521479693/500000000000 : ℝ)*(base39) + (281053493969/500000000000 : ℝ)*(base40) + (195725736191/500000000000 : ℝ)*(base49) + (91/200000000000 : ℝ)*(base60) + (7299/4000 : ℝ)*(major_s1_0) + (7299/4000 : ℝ)*(major_s1_1) + (1824750000793/1000000000000 : ℝ)*(major_s1_2) + (2618295589483/1000000000000 : ℝ)*(sp_s1_0) + (523659118409/200000000000 : ℝ)*(sp_s1_1) + (2618295591299/1000000000000 : ℝ)*(sp_s1_2) + (999999999507/1000000000000 : ℝ)*(sp_s1_6) + (65457389769/25000000000 : ℝ)*(f.sum) + (12478838154136455447/27875413150000000000000000000000 : ℝ)*base63 + (68587023951/549230957031250000000000 : ℝ)*base64 + (100480819564779/123910000000000000000000000 : ℝ)*base67 + (648132951880221/1124825000000000000000000000 : ℝ)*base69 + (14357772127870336849/49107609850000000000000000000000 : ℝ)*base70 + (263796107252439/218290000000000000000000000 : ℝ)*base73 + (25336588406451/123910000000000000000000000 : ℝ)*base75 + (15441133679031/27286250000000000000000000 : ℝ)*base76 + (2545892901380657509/2704831390000000000000000000000 : ℝ)*base79 + (253/1000000000000 : ℝ)*base81 + (253/1000000000000 : ℝ)*base83 + (539/1000000000000 : ℝ)*base85 + (793/1000000000000 : ℝ)*base90 + (539/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p018_b017 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c318037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b017 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
