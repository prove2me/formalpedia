-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p004_b022
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:12.465308+00:00
-- url     : https://prove2.me/submissions/c3fd02e3-5cf0-4963-8eea-f54d9aa20861

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
theorem collision_support_c304041_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1304306593/5000000000 : ℝ)*x 0 + (-5968115869/10000000000 : ℝ)*x 1 + (833399931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1304306593/5000000000 : ℝ)^17 ≤ (17252158303291/100000000000000 : ℝ)^13 := by
    have hnat : (1304306593 : ℕ)^17*100000000000000^13 ≤ 17252158303291^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304306593 5000000000 17252158303291 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5968115869/10000000000 : ℝ)^17 ≤ (50917150521739/100000000000000 : ℝ)^13 := by
    have hnat : (5968115869 : ℕ)^17*100000000000000^13 ≤ 50917150521739^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968115869 10000000000 50917150521739 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833399931/2000000000 : ℝ)^17 ≤ (31830691169321/100000000000000 : ℝ)^13 := by
    have hnat : (833399931 : ℕ)^17*100000000000000^13 ≤ 31830691169321^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833399931 2000000000 31830691169321 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1304306593/5000000000 : ℝ), (-5968115869/10000000000 : ℝ), (833399931/2000000000 : ℝ)] ![(17252158303291/100000000000000 : ℝ), (50917150521739/100000000000000 : ℝ), (31830691169321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1304306593/5000000000 : ℝ)|^17 ≤ (17252158303291/100000000000000 : ℝ)^13
        have hw : |(-1304306593/5000000000 : ℝ)|=(1304306593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5968115869/10000000000 : ℝ)|^17 ≤ (50917150521739/100000000000000 : ℝ)^13
        have hw : |(-5968115869/10000000000 : ℝ)|=(5968115869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833399931/2000000000 : ℝ)|^17 ≤ (31830691169321/100000000000000 : ℝ)^13
        have hw : |(833399931/2000000000 : ℝ)|=(833399931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1155779227/5000000000 : ℝ)*x 0 + (682586513/1250000000 : ℝ)*x 1 + (123915827/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1155779227/5000000000 : ℝ)^17 ≤ (14729340601067/100000000000000 : ℝ)^13 := by
    have hnat : (1155779227 : ℕ)^17*100000000000000^13 ≤ 14729340601067^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155779227 5000000000 14729340601067 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682586513/1250000000 : ℝ)^17 ≤ (45331576759731/100000000000000 : ℝ)^13 := by
    have hnat : (682586513 : ℕ)^17*100000000000000^13 ≤ 45331576759731^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682586513 1250000000 45331576759731 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123915827/250000000 : ℝ)^17 ≤ (39939082620619/100000000000000 : ℝ)^13 := by
    have hnat : (123915827 : ℕ)^17*100000000000000^13 ≤ 39939082620619^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123915827 250000000 39939082620619 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1155779227/5000000000 : ℝ), (682586513/1250000000 : ℝ), (123915827/250000000 : ℝ)] ![(14729340601067/100000000000000 : ℝ), (45331576759731/100000000000000 : ℝ), (39939082620619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1155779227/5000000000 : ℝ)|^17 ≤ (14729340601067/100000000000000 : ℝ)^13
        have hw : |(1155779227/5000000000 : ℝ)|=(1155779227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682586513/1250000000 : ℝ)|^17 ≤ (45331576759731/100000000000000 : ℝ)^13
        have hw : |(682586513/1250000000 : ℝ)|=(682586513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123915827/250000000 : ℝ)|^17 ≤ (39939082620619/100000000000000 : ℝ)^13
        have hw : |(123915827/250000000 : ℝ)|=(123915827/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (57652633/78125000 : ℝ)*x 0 + (-2635522393/10000000000 : ℝ)*x 1 + (-297563367/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57652633/78125000 : ℝ)^17 ≤ (33604132966663/50000000000000 : ℝ)^13 := by
    have hnat : (57652633 : ℕ)^17*50000000000000^13 ≤ 33604132966663^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57652633 78125000 33604132966663 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635522393/10000000000 : ℝ)^17 ≤ (349705004983/2000000000000 : ℝ)^13 := by
    have hnat : (2635522393 : ℕ)^17*2000000000000^13 ≤ 349705004983^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635522393 10000000000 349705004983 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297563367/1250000000 : ℝ)^17 ≤ (7653241900069/50000000000000 : ℝ)^13 := by
    have hnat : (297563367 : ℕ)^17*50000000000000^13 ≤ 7653241900069^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297563367 1250000000 7653241900069 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(57652633/78125000 : ℝ), (-2635522393/10000000000 : ℝ), (-297563367/1250000000 : ℝ)] ![(33604132966663/50000000000000 : ℝ), (349705004983/2000000000000 : ℝ), (7653241900069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(57652633/78125000 : ℝ)|^17 ≤ (33604132966663/50000000000000 : ℝ)^13
        have hw : |(57652633/78125000 : ℝ)|=(57652633/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2635522393/10000000000 : ℝ)|^17 ≤ (349705004983/2000000000000 : ℝ)^13
        have hw : |(-2635522393/10000000000 : ℝ)|=(2635522393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-297563367/1250000000 : ℝ)|^17 ≤ (7653241900069/50000000000000 : ℝ)^13
        have hw : |(-297563367/1250000000 : ℝ)|=(297563367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (940231673/2500000000 : ℝ)*x 0 + (-867713851/5000000000 : ℝ)*x 1 + (6941421659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940231673/2500000000 : ℝ)^17 ≤ (1739788210231/6250000000000 : ℝ)^13 := by
    have hnat : (940231673 : ℕ)^17*6250000000000^13 ≤ 1739788210231^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940231673 2500000000 1739788210231 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (867713851/5000000000 : ℝ)^17 ≤ (10124597437557/100000000000000 : ℝ)^13 := by
    have hnat : (867713851 : ℕ)^17*100000000000000^13 ≤ 10124597437557^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867713851 5000000000 10124597437557 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6941421659/10000000000 : ℝ)^17 ≤ (12407758236403/20000000000000 : ℝ)^13 := by
    have hnat : (6941421659 : ℕ)^17*20000000000000^13 ≤ 12407758236403^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6941421659 10000000000 12407758236403 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(940231673/2500000000 : ℝ), (-867713851/5000000000 : ℝ), (6941421659/10000000000 : ℝ)] ![(1739788210231/6250000000000 : ℝ), (10124597437557/100000000000000 : ℝ), (12407758236403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(940231673/2500000000 : ℝ)|^17 ≤ (1739788210231/6250000000000 : ℝ)^13
        have hw : |(940231673/2500000000 : ℝ)|=(940231673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-867713851/5000000000 : ℝ)|^17 ≤ (10124597437557/100000000000000 : ℝ)^13
        have hw : |(-867713851/5000000000 : ℝ)|=(867713851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6941421659/10000000000 : ℝ)|^17 ≤ (12407758236403/20000000000000 : ℝ)^13
        have hw : |(6941421659/10000000000 : ℝ)|=(6941421659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1929948317/10000000000 : ℝ)*x 0 + (-562247989/1250000000 : ℝ)*x 1 + (385673041/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1929948317/10000000000 : ℝ)^17 ≤ (1454198168123/12500000000000 : ℝ)^13 := by
    have hnat : (1929948317 : ℕ)^17*12500000000000^13 ≤ 1454198168123^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929948317 10000000000 1454198168123 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562247989/1250000000 : ℝ)^17 ≤ (35176625404089/100000000000000 : ℝ)^13 := by
    have hnat : (562247989 : ℕ)^17*100000000000000^13 ≤ 35176625404089^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562247989 1250000000 35176625404089 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385673041/625000000 : ℝ)^17 ≤ (26594894619899/50000000000000 : ℝ)^13 := by
    have hnat : (385673041 : ℕ)^17*50000000000000^13 ≤ 26594894619899^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385673041 625000000 26594894619899 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1929948317/10000000000 : ℝ), (-562247989/1250000000 : ℝ), (385673041/625000000 : ℝ)] ![(1454198168123/12500000000000 : ℝ), (35176625404089/100000000000000 : ℝ), (26594894619899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1929948317/10000000000 : ℝ)|^17 ≤ (1454198168123/12500000000000 : ℝ)^13
        have hw : |(-1929948317/10000000000 : ℝ)|=(1929948317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562247989/1250000000 : ℝ)|^17 ≤ (35176625404089/100000000000000 : ℝ)^13
        have hw : |(-562247989/1250000000 : ℝ)|=(562247989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385673041/625000000 : ℝ)|^17 ≤ (26594894619899/50000000000000 : ℝ)^13
        have hw : |(385673041/625000000 : ℝ)|=(385673041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1965920779/10000000000 : ℝ)*x 0 + (5688862137/10000000000 : ℝ)*x 1 + (4986847207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965920779/10000000000 : ℝ)^17 ≤ (2383590824687/20000000000000 : ℝ)^13 := by
    have hnat : (1965920779 : ℕ)^17*20000000000000^13 ≤ 2383590824687^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965920779 10000000000 2383590824687 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5688862137/10000000000 : ℝ)^17 ≤ (1912971956421/4000000000000 : ℝ)^13 := by
    have hnat : (5688862137 : ℕ)^17*4000000000000^13 ≤ 1912971956421^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688862137 10000000000 1912971956421 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986847207/10000000000 : ℝ)^17 ≤ (1610309878021/4000000000000 : ℝ)^13 := by
    have hnat : (4986847207 : ℕ)^17*4000000000000^13 ≤ 1610309878021^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986847207 10000000000 1610309878021 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1965920779/10000000000 : ℝ), (5688862137/10000000000 : ℝ), (4986847207/10000000000 : ℝ)] ![(2383590824687/20000000000000 : ℝ), (1912971956421/4000000000000 : ℝ), (1610309878021/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1965920779/10000000000 : ℝ)|^17 ≤ (2383590824687/20000000000000 : ℝ)^13
        have hw : |(1965920779/10000000000 : ℝ)|=(1965920779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5688862137/10000000000 : ℝ)|^17 ≤ (1912971956421/4000000000000 : ℝ)^13
        have hw : |(5688862137/10000000000 : ℝ)|=(5688862137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986847207/10000000000 : ℝ)|^17 ≤ (1610309878021/4000000000000 : ℝ)^13
        have hw : |(4986847207/10000000000 : ℝ)|=(4986847207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1697825859/2000000000 : ℝ)*x 0 + (-35607177/200000000 : ℝ)*x 1 + (-390164911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1697825859/2000000000 : ℝ)^17 ≤ (10089854397161/12500000000000 : ℝ)^13 := by
    have hnat : (1697825859 : ℕ)^17*12500000000000^13 ≤ 10089854397161^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697825859 2000000000 10089854397161 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35607177/200000000 : ℝ)^17 ≤ (5234370863423/50000000000000 : ℝ)^13 := by
    have hnat : (35607177 : ℕ)^17*50000000000000^13 ≤ 5234370863423^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35607177 200000000 5234370863423 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390164911/2500000000 : ℝ)^17 ≤ (176248461499/2000000000000 : ℝ)^13 := by
    have hnat : (390164911 : ℕ)^17*2000000000000^13 ≤ 176248461499^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390164911 2500000000 176248461499 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1697825859/2000000000 : ℝ), (-35607177/200000000 : ℝ), (-390164911/2500000000 : ℝ)] ![(10089854397161/12500000000000 : ℝ), (5234370863423/50000000000000 : ℝ), (176248461499/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1697825859/2000000000 : ℝ)|^17 ≤ (10089854397161/12500000000000 : ℝ)^13
        have hw : |(1697825859/2000000000 : ℝ)|=(1697825859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35607177/200000000 : ℝ)|^17 ≤ (5234370863423/50000000000000 : ℝ)^13
        have hw : |(-35607177/200000000 : ℝ)|=(35607177/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390164911/2500000000 : ℝ)|^17 ≤ (176248461499/2000000000000 : ℝ)^13
        have hw : |(-390164911/2500000000 : ℝ)|=(390164911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (515024871/1000000000 : ℝ)*x 0 + (-3260121761/10000000000 : ℝ)*x 1 + (4472549829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515024871/1000000000 : ℝ)^17 ≤ (41991361531757/100000000000000 : ℝ)^13 := by
    have hnat : (515024871 : ℕ)^17*100000000000000^13 ≤ 41991361531757^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515024871 1000000000 41991361531757 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3260121761/10000000000 : ℝ)^17 ≤ (11545948498687/50000000000000 : ℝ)^13 := by
    have hnat : (3260121761 : ℕ)^17*50000000000000^13 ≤ 11545948498687^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3260121761 10000000000 11545948498687 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4472549829/10000000000 : ℝ)^17 ≤ (34916741450983/100000000000000 : ℝ)^13 := by
    have hnat : (4472549829 : ℕ)^17*100000000000000^13 ≤ 34916741450983^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472549829 10000000000 34916741450983 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515024871/1000000000 : ℝ), (-3260121761/10000000000 : ℝ), (4472549829/10000000000 : ℝ)] ![(41991361531757/100000000000000 : ℝ), (11545948498687/50000000000000 : ℝ), (34916741450983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515024871/1000000000 : ℝ)|^17 ≤ (41991361531757/100000000000000 : ℝ)^13
        have hw : |(515024871/1000000000 : ℝ)|=(515024871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3260121761/10000000000 : ℝ)|^17 ≤ (11545948498687/50000000000000 : ℝ)^13
        have hw : |(-3260121761/10000000000 : ℝ)|=(3260121761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4472549829/10000000000 : ℝ)|^17 ≤ (34916741450983/100000000000000 : ℝ)^13
        have hw : |(4472549829/10000000000 : ℝ)|=(4472549829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-673254809/2500000000 : ℝ)*x 0 + (-5283037179/10000000000 : ℝ)*x 1 + (4829186351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673254809/2500000000 : ℝ)^17 ≤ (4496437151333/25000000000000 : ℝ)^13 := by
    have hnat : (673254809 : ℕ)^17*25000000000000^13 ≤ 4496437151333^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673254809 2500000000 4496437151333 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5283037179/10000000000 : ℝ)^17 ≤ (4341273058059/10000000000000 : ℝ)^13 := by
    have hnat : (5283037179 : ℕ)^17*10000000000000^13 ≤ 4341273058059^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283037179 10000000000 4341273058059 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829186351/10000000000 : ℝ)^17 ≤ (19300760400737/50000000000000 : ℝ)^13 := by
    have hnat : (4829186351 : ℕ)^17*50000000000000^13 ≤ 19300760400737^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829186351 10000000000 19300760400737 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-673254809/2500000000 : ℝ), (-5283037179/10000000000 : ℝ), (4829186351/10000000000 : ℝ)] ![(4496437151333/25000000000000 : ℝ), (4341273058059/10000000000000 : ℝ), (19300760400737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-673254809/2500000000 : ℝ)|^17 ≤ (4496437151333/25000000000000 : ℝ)^13
        have hw : |(-673254809/2500000000 : ℝ)|=(673254809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5283037179/10000000000 : ℝ)|^17 ≤ (4341273058059/10000000000000 : ℝ)^13
        have hw : |(-5283037179/10000000000 : ℝ)|=(5283037179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829186351/10000000000 : ℝ)|^17 ≤ (19300760400737/50000000000000 : ℝ)^13
        have hw : |(4829186351/10000000000 : ℝ)|=(4829186351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (938659839/5000000000 : ℝ)*x 0 + (718381493/1250000000 : ℝ)*x 1 + (4992223767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938659839/5000000000 : ℝ)^17 ≤ (11220482551491/100000000000000 : ℝ)^13 := by
    have hnat : (938659839 : ℕ)^17*100000000000000^13 ≤ 11220482551491^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938659839 5000000000 11220482551491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718381493/1250000000 : ℝ)^17 ≤ (48465002231777/100000000000000 : ℝ)^13 := by
    have hnat : (718381493 : ℕ)^17*100000000000000^13 ≤ 48465002231777^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718381493 1250000000 48465002231777 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4992223767/10000000000 : ℝ)^17 ≤ (10078628799319/25000000000000 : ℝ)^13 := by
    have hnat : (4992223767 : ℕ)^17*25000000000000^13 ≤ 10078628799319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992223767 10000000000 10078628799319 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(938659839/5000000000 : ℝ), (718381493/1250000000 : ℝ), (4992223767/10000000000 : ℝ)] ![(11220482551491/100000000000000 : ℝ), (48465002231777/100000000000000 : ℝ), (10078628799319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(938659839/5000000000 : ℝ)|^17 ≤ (11220482551491/100000000000000 : ℝ)^13
        have hw : |(938659839/5000000000 : ℝ)|=(938659839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(718381493/1250000000 : ℝ)|^17 ≤ (48465002231777/100000000000000 : ℝ)^13
        have hw : |(718381493/1250000000 : ℝ)|=(718381493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4992223767/10000000000 : ℝ)|^17 ≤ (10078628799319/25000000000000 : ℝ)^13
        have hw : |(4992223767/10000000000 : ℝ)|=(4992223767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9023069371/10000000000 : ℝ)*x 0 + (-257921389/2000000000 : ℝ)*x 1 + (-28005691/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9023069371/10000000000 : ℝ)^17 ≤ (21855319783181/25000000000000 : ℝ)^13 := by
    have hnat : (9023069371 : ℕ)^17*25000000000000^13 ≤ 21855319783181^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9023069371 10000000000 21855319783181 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257921389/2000000000 : ℝ)^17 ≤ (858345134361/12500000000000 : ℝ)^13 := by
    have hnat : (257921389 : ℕ)^17*12500000000000^13 ≤ 858345134361^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257921389 2000000000 858345134361 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28005691/250000000 : ℝ)^17 ≤ (5711959779133/100000000000000 : ℝ)^13 := by
    have hnat : (28005691 : ℕ)^17*100000000000000^13 ≤ 5711959779133^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28005691 250000000 5711959779133 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9023069371/10000000000 : ℝ), (-257921389/2000000000 : ℝ), (-28005691/250000000 : ℝ)] ![(21855319783181/25000000000000 : ℝ), (858345134361/12500000000000 : ℝ), (5711959779133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9023069371/10000000000 : ℝ)|^17 ≤ (21855319783181/25000000000000 : ℝ)^13
        have hw : |(9023069371/10000000000 : ℝ)|=(9023069371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257921389/2000000000 : ℝ)|^17 ≤ (858345134361/12500000000000 : ℝ)^13
        have hw : |(-257921389/2000000000 : ℝ)|=(257921389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28005691/250000000 : ℝ)|^17 ≤ (5711959779133/100000000000000 : ℝ)^13
        have hw : |(-28005691/250000000 : ℝ)|=(28005691/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s0_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (673254809/2500000000 : ℝ)*x 0 + (-5283037179/10000000000 : ℝ)*x 1 + (4829186351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673254809/2500000000 : ℝ)^17 ≤ (4496437151333/25000000000000 : ℝ)^13 := by
    have hnat : (673254809 : ℕ)^17*25000000000000^13 ≤ 4496437151333^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673254809 2500000000 4496437151333 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5283037179/10000000000 : ℝ)^17 ≤ (4341273058059/10000000000000 : ℝ)^13 := by
    have hnat : (5283037179 : ℕ)^17*10000000000000^13 ≤ 4341273058059^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283037179 10000000000 4341273058059 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829186351/10000000000 : ℝ)^17 ≤ (19300760400737/50000000000000 : ℝ)^13 := by
    have hnat : (4829186351 : ℕ)^17*50000000000000^13 ≤ 19300760400737^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829186351 10000000000 19300760400737 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673254809/2500000000 : ℝ), (-5283037179/10000000000 : ℝ), (4829186351/10000000000 : ℝ)] ![(4496437151333/25000000000000 : ℝ), (4341273058059/10000000000000 : ℝ), (19300760400737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673254809/2500000000 : ℝ)|^17 ≤ (4496437151333/25000000000000 : ℝ)^13
        have hw : |(673254809/2500000000 : ℝ)|=(673254809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5283037179/10000000000 : ℝ)|^17 ≤ (4341273058059/10000000000000 : ℝ)^13
        have hw : |(-5283037179/10000000000 : ℝ)|=(5283037179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829186351/10000000000 : ℝ)|^17 ≤ (19300760400737/50000000000000 : ℝ)^13
        have hw : |(4829186351/10000000000 : ℝ)|=(4829186351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3462350973/10000000000 : ℝ)*x 0 + (-852601437/2000000000 : ℝ)*x 1 + (1293018397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3462350973/10000000000 : ℝ)^17 ≤ (12491342642391/50000000000000 : ℝ)^13 := by
    have hnat : (3462350973 : ℕ)^17*50000000000000^13 ≤ 12491342642391^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462350973 10000000000 12491342642391 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852601437/2000000000 : ℝ)^17 ≤ (32793105487317/100000000000000 : ℝ)^13 := by
    have hnat : (852601437 : ℕ)^17*100000000000000^13 ≤ 32793105487317^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852601437 2000000000 32793105487317 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293018397/2500000000 : ℝ)^17 ≤ (10556052302977/25000000000000 : ℝ)^13 := by
    have hnat : (1293018397 : ℕ)^17*25000000000000^13 ≤ 10556052302977^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293018397 2500000000 10556052302977 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3462350973/10000000000 : ℝ), (-852601437/2000000000 : ℝ), (1293018397/2500000000 : ℝ)] ![(12491342642391/50000000000000 : ℝ), (32793105487317/100000000000000 : ℝ), (10556052302977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3462350973/10000000000 : ℝ)|^17 ≤ (12491342642391/50000000000000 : ℝ)^13
        have hw : |(-3462350973/10000000000 : ℝ)|=(3462350973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852601437/2000000000 : ℝ)|^17 ≤ (32793105487317/100000000000000 : ℝ)^13
        have hw : |(-852601437/2000000000 : ℝ)|=(852601437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293018397/2500000000 : ℝ)|^17 ≤ (10556052302977/25000000000000 : ℝ)^13
        have hw : |(1293018397/2500000000 : ℝ)|=(1293018397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3927784073/10000000000 : ℝ)*x 0 + (243139687/500000000 : ℝ)*x 1 + (414230981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3927784073/10000000000 : ℝ)^17 ≤ (29462523686209/100000000000000 : ℝ)^13 := by
    have hnat : (3927784073 : ℕ)^17*100000000000000^13 ≤ 29462523686209^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3927784073 10000000000 29462523686209 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243139687/500000000 : ℝ)^17 ≤ (38953190360949/100000000000000 : ℝ)^13 := by
    have hnat : (243139687 : ℕ)^17*100000000000000^13 ≤ 38953190360949^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243139687 500000000 38953190360949 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414230981/1000000000 : ℝ)^17 ≤ (31584285933843/100000000000000 : ℝ)^13 := by
    have hnat : (414230981 : ℕ)^17*100000000000000^13 ≤ 31584285933843^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414230981 1000000000 31584285933843 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3927784073/10000000000 : ℝ), (243139687/500000000 : ℝ), (414230981/1000000000 : ℝ)] ![(29462523686209/100000000000000 : ℝ), (38953190360949/100000000000000 : ℝ), (31584285933843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3927784073/10000000000 : ℝ)|^17 ≤ (29462523686209/100000000000000 : ℝ)^13
        have hw : |(3927784073/10000000000 : ℝ)|=(3927784073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243139687/500000000 : ℝ)|^17 ≤ (38953190360949/100000000000000 : ℝ)^13
        have hw : |(243139687/500000000 : ℝ)|=(243139687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414230981/1000000000 : ℝ)|^17 ≤ (31584285933843/100000000000000 : ℝ)^13
        have hw : |(414230981/1000000000 : ℝ)|=(414230981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5445621581/10000000000 : ℝ)*x 0 + (-1002715199/2500000000 : ℝ)*x 1 + (-136664057/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5445621581/10000000000 : ℝ)^17 ≤ (11292011215583/25000000000000 : ℝ)^13 := by
    have hnat : (5445621581 : ℕ)^17*25000000000000^13 ≤ 11292011215583^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445621581 10000000000 11292011215583 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002715199/2500000000 : ℝ)^17 ≤ (1892504256119/6250000000000 : ℝ)^13 := by
    have hnat : (1002715199 : ℕ)^17*6250000000000^13 ≤ 1892504256119^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002715199 2500000000 1892504256119 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136664057/400000000 : ℝ)^17 ≤ (24551887021823/100000000000000 : ℝ)^13 := by
    have hnat : (136664057 : ℕ)^17*100000000000000^13 ≤ 24551887021823^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136664057 400000000 24551887021823 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5445621581/10000000000 : ℝ), (-1002715199/2500000000 : ℝ), (-136664057/400000000 : ℝ)] ![(11292011215583/25000000000000 : ℝ), (1892504256119/6250000000000 : ℝ), (24551887021823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5445621581/10000000000 : ℝ)|^17 ≤ (11292011215583/25000000000000 : ℝ)^13
        have hw : |(5445621581/10000000000 : ℝ)|=(5445621581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002715199/2500000000 : ℝ)|^17 ≤ (1892504256119/6250000000000 : ℝ)^13
        have hw : |(-1002715199/2500000000 : ℝ)|=(1002715199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136664057/400000000 : ℝ)|^17 ≤ (24551887021823/100000000000000 : ℝ)^13
        have hw : |(-136664057/400000000 : ℝ)|=(136664057/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304041_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4339984/9765625 : ℝ)*x 0 + (-3837202699/10000000000 : ℝ)*x 1 + (4655468281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339984/9765625 : ℝ)^17 ≤ (34627025610631/100000000000000 : ℝ)^13 := by
    have hnat : (4339984 : ℕ)^17*100000000000000^13 ≤ 34627025610631^13*9765625^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339984 9765625 34627025610631 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3837202699/10000000000 : ℝ)^17 ≤ (28577173861749/100000000000000 : ℝ)^13 := by
    have hnat : (3837202699 : ℕ)^17*100000000000000^13 ≤ 28577173861749^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837202699 10000000000 28577173861749 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4655468281/10000000000 : ℝ)^17 ≤ (7359160103343/20000000000000 : ℝ)^13 := by
    have hnat : (4655468281 : ℕ)^17*20000000000000^13 ≤ 7359160103343^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655468281 10000000000 7359160103343 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339984/9765625 : ℝ), (-3837202699/10000000000 : ℝ), (4655468281/10000000000 : ℝ)] ![(34627025610631/100000000000000 : ℝ), (28577173861749/100000000000000 : ℝ), (7359160103343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339984/9765625 : ℝ)|^17 ≤ (34627025610631/100000000000000 : ℝ)^13
        have hw : |(4339984/9765625 : ℝ)|=(4339984/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3837202699/10000000000 : ℝ)|^17 ≤ (28577173861749/100000000000000 : ℝ)^13
        have hw : |(-3837202699/10000000000 : ℝ)|=(3837202699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4655468281/10000000000 : ℝ)|^17 ≤ (7359160103343/20000000000000 : ℝ)^13
        have hw : |(4655468281/10000000000 : ℝ)|=(4655468281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304041 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_7 : ((-1304306593/5000000000 : ℝ)*X 0 0+(-5968115869/10000000000 : ℝ)*X 0 1+(833399931/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1155779227/5000000000 : ℝ)*X 1 0+(682586513/1250000000 : ℝ)*X 1 1+(123915827/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((57652633/78125000 : ℝ)*X 2 0+(-2635522393/10000000000 : ℝ)*X 2 1+(-297563367/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((940231673/2500000000 : ℝ)*X 0 0+(-867713851/5000000000 : ℝ)*X 0 1+(6941421659/10000000000 : ℝ)*X 0 2+(940231673/2500000000 : ℝ)*X 1 0+(-867713851/5000000000 : ℝ)*X 1 1+(6941421659/10000000000 : ℝ)*X 1 2+(940231673/2500000000 : ℝ)*X 2 0+(-867713851/5000000000 : ℝ)*X 2 1+(6941421659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1929948317/10000000000 : ℝ)*X 0 0+(-562247989/1250000000 : ℝ)*X 0 1+(385673041/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1965920779/10000000000 : ℝ)*X 1 0+(5688862137/10000000000 : ℝ)*X 1 1+(4986847207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1697825859/2000000000 : ℝ)*X 2 0+(-35607177/200000000 : ℝ)*X 2 1+(-390164911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((515024871/1000000000 : ℝ)*X 0 0+(-3260121761/10000000000 : ℝ)*X 0 1+(4472549829/10000000000 : ℝ)*X 0 2+(515024871/1000000000 : ℝ)*X 1 0+(-3260121761/10000000000 : ℝ)*X 1 1+(4472549829/10000000000 : ℝ)*X 1 2+(515024871/1000000000 : ℝ)*X 2 0+(-3260121761/10000000000 : ℝ)*X 2 1+(4472549829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-673254809/2500000000 : ℝ)*X 0 0+(-5283037179/10000000000 : ℝ)*X 0 1+(4829186351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((938659839/5000000000 : ℝ)*X 1 0+(718381493/1250000000 : ℝ)*X 1 1+(4992223767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9023069371/10000000000 : ℝ)*X 2 0+(-257921389/2000000000 : ℝ)*X 2 1+(-28005691/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((673254809/2500000000 : ℝ)*X 0 0+(-5283037179/10000000000 : ℝ)*X 0 1+(4829186351/10000000000 : ℝ)*X 0 2+(673254809/2500000000 : ℝ)*X 1 0+(-5283037179/10000000000 : ℝ)*X 1 1+(4829186351/10000000000 : ℝ)*X 1 2+(673254809/2500000000 : ℝ)*X 2 0+(-5283037179/10000000000 : ℝ)*X 2 1+(4829186351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((14751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (471152433882120607659/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (931953/200000000000 : ℝ)*(base1) + (1875263/500000000000 : ℝ)*(base3) + (922069/200000000000 : ℝ)*(base40) + (151555821869/500000000000 : ℝ)*(base50) + (594496427649/1000000000000 : ℝ)*(base60) + (178949446821/62500000000 : ℝ)*(major_s0_0) + (178949446821/62500000000 : ℝ)*(major_s0_1) + (178949446821/62500000000 : ℝ)*(major_s0_2) + (3838566017811/1000000000000 : ℝ)*(sp_s0_7) + (3838421822329/1000000000000 : ℝ)*(sp_s0_8) + (3838627827847/1000000000000 : ℝ)*(sp_s0_9) + (117983971707/62500000000 : ℝ)*(sp_s0_13) + (41951209/200000000000 : ℝ)*(sp_s0_15) + (33234901/500000000000 : ℝ)*(sp_s0_20) + (471937989401/250000000000 : ℝ)*(f.failure) + (3838627827847/1000000000000 : ℝ)*(f.sum) + (1109457607/5000000000000000000000 : ℝ)*base63 + (2758673404599/3125000000000000000000000 : ℝ)*base65 + (1150588260737/1562500000000000000000000 : ℝ)*base66 + (46263321240053/125000000000000000000000000 : ℝ)*base68 + (86127242863487/125000000000000000000000000 : ℝ)*base70 + (92890124487/1562500000000000000000000 : ℝ)*base72 + (36715298222447/125000000000000000000000000 : ℝ)*base74 + (26586871634947/125000000000000000000000000 : ℝ)*base76 + (1294938461427/3125000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (3559/3125000000000000 : ℝ)*base87 + (3559/3125000000000000 : ℝ)*base89 + (3559/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30647/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-30647/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1866793259814530001927/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132167/10000000000 : ℝ)*(base5) + (387988769951/1000000000000 : ℝ)*(base39) + (926579938667/1000000000000 : ℝ)*(base40) + (90721461363/125000000000 : ℝ)*(base60) + (424150714373/125000000000 : ℝ)*(major_s0_0) + (424150714373/125000000000 : ℝ)*(major_s0_1) + (424150714373/125000000000 : ℝ)*(major_s0_2) + (138724861/500000000000 : ℝ)*(sp_s0_8) + (24646467/1000000000000 : ℝ)*(sp_s0_9) + (4558207/125000000000 : ℝ)*(sp_s0_13) + (909841325843/200000000000 : ℝ)*(sp_s0_14) + (2274464589747/500000000000 : ℝ)*(sp_s0_15) + (568649399931/125000000000 : ℝ)*(sp_s0_16) + (1118575070139/500000000000 : ℝ)*(sp_s0_19) + (2237199822633/1000000000000 : ℝ)*(f.failure) + (909841325843/200000000000 : ℝ)*(f.sum) + (3347950177/10000000000000000000000 : ℝ)*base62 + (2141714959451/12500000000000000000000000 : ℝ)*base64 + (952359610549/12500000000000000000000000 : ℝ)*base66 + (77599618628289/250000000000000000000000000 : ℝ)*base68 + (117724425360731/250000000000000000000000000 : ℝ)*base70 + (4979474583049/12500000000000000000000000 : ℝ)*base72 + (32568922521711/250000000000000000000000000 : ℝ)*base74 + (38686494996711/250000000000000000000000000 : ℝ)*base76 + (1326861191799/6250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (953/12500000000000000 : ℝ)*base86 + (953/12500000000000000 : ℝ)*base88 + (953/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(22481/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(22481/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (254145532555043855673/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (241510884393/200000000000 : ℝ)*(base1) + (308733725541/500000000000 : ℝ)*(base39) + (1257485692571/1000000000000 : ℝ)*(base40) + (20529978081/200000000000 : ℝ)*(base50) + (137346452647/1000000000000 : ℝ)*(base60) + (130898738067/62500000000 : ℝ)*(major_s0_0) + (130898738067/62500000000 : ℝ)*(major_s0_1) + (130898738067/62500000000 : ℝ)*(major_s0_2) + (4674043/100000000000 : ℝ)*(sp_s0_7) + (262161993/1000000000000 : ℝ)*(sp_s0_15) + (4015404737759/1000000000000 : ℝ)*(sp_s0_20) + (2807634894231/1000000000000 : ℝ)*(sp_s0_21) + (87746783007/31250000000 : ℝ)*(sp_s0_22) + (173306784501/1000000000000 : ℝ)*(sp_s0_25) + (690430603233/500000000000 : ℝ)*(f.failure) + (87746783007/31250000000 : ℝ)*(f.sum) + (510045217/2500000000000000000000 : ℝ)*base63 + (7778556354079/6250000000000000000000000 : ℝ)*base64 + (6005908416579/6250000000000000000000000 : ℝ)*base67 + (113541064140869/125000000000000000000000000 : ℝ)*base69 + (57831079184949/125000000000000000000000000 : ℝ)*base70 + (3340043999227/3125000000000000000000000 : ℝ)*base73 + (65879339096631/125000000000000000000000000 : ℝ)*base75 + (64260477165869/125000000000000000000000000 : ℝ)*base76 + (5167901413783/6250000000000000000000000 : ℝ)*base79 + (5553/6250000000000000 : ℝ)*base86 + (5553/6250000000000000 : ℝ)*base88 + (5553/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (14751/100000 : ℝ) ^ (33/8 : ℝ) ≤ (18636250493447307/50000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^33 ≤ (18636250493447307/50000000000000000000 : ℝ)^8 := by
      have hnat : (14751 : ℕ)^33*50000000000000000000^8 ≤ 18636250493447307^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 18636250493447307 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (18636250493447307/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50018636250493447307/50000000000000000000 : ℝ) ≤ (2500225862059791/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50018636250493447307/50000000000000000000 : ℝ)^8 ≤ (2500225862059791/2500000000000000 : ℝ)^33 := by
      have hnat : (50018636250493447307 : ℕ)^8*2500000000000000^33 ≤ 2500225862059791^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018636250493447307 50000000000000000000 2500225862059791 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500225862059791/2500000000000000 : ℝ)) (X := (50018636250493447307/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25018636250493447307/25000000000000000000 : ℝ) ≤ (2000361328300999/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25018636250493447307/25000000000000000000 : ℝ)^8 ≤ (2000361328300999/2000000000000000 : ℝ)^33 := by
      have hnat : (25018636250493447307 : ℕ)^8*2000000000000000^33 ≤ 2000361328300999^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018636250493447307 25000000000000000000 2000361328300999 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000361328300999/2000000000000000 : ℝ)) (X := (25018636250493447307/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(225862059791/368775000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903193265831/1475100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (14751/100000 : ℝ)) (alpha := (225862059791/368775000000000 : ℝ)) (beta := (903193265831/1475100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14751/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(225862059791/368775000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903193265831/1475100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30647/100000 : ℝ) ^ (33/8 : ℝ) ≤ (760939921752188283/100000000000000000000 : ℝ) := by
    have hpowers : (30647/100000 : ℝ)^33 ≤ (760939921752188283/100000000000000000000 : ℝ)^8 := by
      have hnat : (30647 : ℕ)^33*100000000000000000000^8 ≤ 760939921752188283^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30647 100000 760939921752188283 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30647/100000 : ℝ)) (X := (760939921752188283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100760939921752188283/100000000000000000000 : ℝ) ≤ (2003678818689549/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100760939921752188283/100000000000000000000 : ℝ)^8 ≤ (2003678818689549/2000000000000000 : ℝ)^33 := by
      have hnat : (100760939921752188283 : ℕ)^8*2000000000000000^33 ≤ 2003678818689549^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100760939921752188283 100000000000000000000 2003678818689549 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003678818689549/2000000000000000 : ℝ)) (X := (100760939921752188283/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50760939921752188283/50000000000000000000 : ℝ) ≤ (401467330016059/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50760939921752188283/50000000000000000000 : ℝ)^8 ≤ (401467330016059/400000000000000 : ℝ)^33 := by
      have hnat : (50760939921752188283 : ℕ)^8*400000000000000^33 ≤ 401467330016059^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50760939921752188283 50000000000000000000 401467330016059 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401467330016059/400000000000000 : ℝ)) (X := (50760939921752188283/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(3678818689549/612940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1828915695373/306470000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (30647/100000 : ℝ)) (alpha := (3678818689549/612940000000000 : ℝ)) (beta := (1828915695373/306470000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30647/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(3678818689549/612940000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1828915695373/306470000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (22481/100000 : ℝ) ^ (33/8 : ℝ) ≤ (52988236296150317/25000000000000000000 : ℝ) := by
    have hpowers : (22481/100000 : ℝ)^33 ≤ (52988236296150317/25000000000000000000 : ℝ)^8 := by
      have hnat : (22481 : ℕ)^33*25000000000000000000^8 ≤ 52988236296150317^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22481 100000 52988236296150317 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22481/100000 : ℝ)) (X := (52988236296150317/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25052988236296150317/25000000000000000000 : ℝ) ≤ (10005134133074433/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25052988236296150317/25000000000000000000 : ℝ)^8 ≤ (10005134133074433/10000000000000000 : ℝ)^33 := by
      have hnat : (25052988236296150317 : ℕ)^8*10000000000000000^33 ≤ 10005134133074433^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25052988236296150317 25000000000000000000 10005134133074433 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005134133074433/10000000000000000 : ℝ)) (X := (25052988236296150317/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12552988236296150317/12500000000000000000 : ℝ) ≤ (2002052009253023/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12552988236296150317/12500000000000000000 : ℝ)^8 ≤ (2002052009253023/2000000000000000 : ℝ)^33 := by
      have hnat : (12552988236296150317 : ℕ)^8*2000000000000000^33 ≤ 2002052009253023^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12552988236296150317 12500000000000000000 2002052009253023 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002052009253023/2000000000000000 : ℝ)) (X := (12552988236296150317/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5134133074433/2248100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2562956595341/1124050000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (22481/100000 : ℝ)) (alpha := (5134133074433/2248100000000000 : ℝ)) (beta := (2562956595341/1124050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (22481/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5134133074433/2248100000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2562956595341/1124050000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3462350973/10000000000 : ℝ)*X 0 0+(-852601437/2000000000 : ℝ)*X 0 1+(1293018397/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3927784073/10000000000 : ℝ)*X 1 0+(243139687/500000000 : ℝ)*X 1 1+(414230981/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5445621581/10000000000 : ℝ)*X 2 0+(-1002715199/2500000000 : ℝ)*X 2 1+(-136664057/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4339984/9765625 : ℝ)*X 0 0+(-3837202699/10000000000 : ℝ)*X 0 1+(4655468281/10000000000 : ℝ)*X 0 2+(4339984/9765625 : ℝ)*X 1 0+(-3837202699/10000000000 : ℝ)*X 1 1+(4655468281/10000000000 : ℝ)*X 1 2+(4339984/9765625 : ℝ)*X 2 0+(-3837202699/10000000000 : ℝ)*X 2 1+(4655468281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304041_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-17082787408648935711609675006229057/2823075910682500000000000000000000 : ℝ) := by norm_num
    linear_combination (459067/500000000000 : ℝ)*(base1) + (335173/1000000000000 : ℝ)*(base13) + (191/1000000000000 : ℝ)*(base17) + (74387/500000000000 : ℝ)*(base22) + (21296519031/200000000000 : ℝ)*(base39) + (323063616119/1000000000000 : ℝ)*(base40) + (8497669793/500000000000 : ℝ)*(base50) + (55318339801/200000000000 : ℝ)*(base60) + (18959/12500 : ℝ)*(major_s1_0) + (18959/12500 : ℝ)*(major_s1_1) + (18959/12500 : ℝ)*(major_s1_2) + (2017042508043/1000000000000 : ℝ)*(sp_s1_0) + (504260481223/250000000000 : ℝ)*(sp_s1_1) + (2017041776309/1000000000000 : ℝ)*(sp_s1_2) + (499999540933/500000000000 : ℝ)*(sp_s1_6) + (2017041925083/1000000000000 : ℝ)*(f.sum) + (629115021539860281/6889752070000000000000000000000 : ℝ)*base63 + (8333147457991/224810000000000000000000000 : ℝ)*base64 + (15145197617239/30647000000000000000000000 : ℝ)*base67 + (2816902932783/56202500000000000000000000 : ℝ)*base68 + (79329009119221663/1658086155000000000000000000000 : ℝ)*base70 + (60042754821817/73755000000000000000000000 : ℝ)*base73 + (29438957247141/61294000000000000000000000 : ℝ)*base75 + (31743110133101/73755000000000000000000000 : ℝ)*base76 + (2315183737061604163/4520738970000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c304042_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1526747987/5000000000 : ℝ)*x 0 + (-4905535447/10000000000 : ℝ)*x 1 + (-1226383861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526747987/5000000000 : ℝ)^17 ≤ (21196954126861/100000000000000 : ℝ)^13 := by
    have hnat : (1526747987 : ℕ)^17*100000000000000^13 ≤ 21196954126861^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526747987 5000000000 21196954126861 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905535447/10000000000 : ℝ)^17 ≤ (7880304588871/20000000000000 : ℝ)^13 := by
    have hnat : (4905535447 : ℕ)^17*20000000000000^13 ≤ 7880304588871^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905535447 10000000000 7880304588871 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1226383861/2500000000 : ℝ)^17 ≤ (9850380728211/25000000000000 : ℝ)^13 := by
    have hnat : (1226383861 : ℕ)^17*25000000000000^13 ≤ 9850380728211^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226383861 2500000000 9850380728211 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1526747987/5000000000 : ℝ), (-4905535447/10000000000 : ℝ), (-1226383861/2500000000 : ℝ)] ![(21196954126861/100000000000000 : ℝ), (7880304588871/20000000000000 : ℝ), (9850380728211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1526747987/5000000000 : ℝ)|^17 ≤ (21196954126861/100000000000000 : ℝ)^13
        have hw : |(-1526747987/5000000000 : ℝ)|=(1526747987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4905535447/10000000000 : ℝ)|^17 ≤ (7880304588871/20000000000000 : ℝ)^13
        have hw : |(-4905535447/10000000000 : ℝ)|=(4905535447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1226383861/2500000000 : ℝ)|^17 ≤ (9850380728211/25000000000000 : ℝ)^13
        have hw : |(-1226383861/2500000000 : ℝ)|=(1226383861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304042_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1526747987/5000000000 : ℝ)*x 0 + (4905535447/10000000000 : ℝ)*x 1 + (-1226383861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526747987/5000000000 : ℝ)^17 ≤ (21196954126861/100000000000000 : ℝ)^13 := by
    have hnat : (1526747987 : ℕ)^17*100000000000000^13 ≤ 21196954126861^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526747987 5000000000 21196954126861 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905535447/10000000000 : ℝ)^17 ≤ (7880304588871/20000000000000 : ℝ)^13 := by
    have hnat : (4905535447 : ℕ)^17*20000000000000^13 ≤ 7880304588871^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905535447 10000000000 7880304588871 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1226383861/2500000000 : ℝ)^17 ≤ (9850380728211/25000000000000 : ℝ)^13 := by
    have hnat : (1226383861 : ℕ)^17*25000000000000^13 ≤ 9850380728211^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226383861 2500000000 9850380728211 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1526747987/5000000000 : ℝ), (4905535447/10000000000 : ℝ), (-1226383861/2500000000 : ℝ)] ![(21196954126861/100000000000000 : ℝ), (7880304588871/20000000000000 : ℝ), (9850380728211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1526747987/5000000000 : ℝ)|^17 ≤ (21196954126861/100000000000000 : ℝ)^13
        have hw : |(1526747987/5000000000 : ℝ)|=(1526747987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4905535447/10000000000 : ℝ)|^17 ≤ (7880304588871/20000000000000 : ℝ)^13
        have hw : |(4905535447/10000000000 : ℝ)|=(4905535447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1226383861/2500000000 : ℝ)|^17 ≤ (9850380728211/25000000000000 : ℝ)^13
        have hw : |(-1226383861/2500000000 : ℝ)|=(1226383861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304042_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5923296331/10000000000 : ℝ)*x 0 + (-430254231/1250000000 : ℝ)*x 1 + (3442033847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5923296331/10000000000 : ℝ)^17 ≤ (78777648363/156250000000 : ℝ)^13 := by
    have hnat : (5923296331 : ℕ)^17*156250000000^13 ≤ 78777648363^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923296331 10000000000 78777648363 156250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430254231/1250000000 : ℝ)^17 ≤ (247911525231/1000000000000 : ℝ)^13 := by
    have hnat : (430254231 : ℕ)^17*1000000000000^13 ≤ 247911525231^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430254231 1250000000 247911525231 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3442033847/10000000000 : ℝ)^17 ≤ (12395576256841/50000000000000 : ℝ)^13 := by
    have hnat : (3442033847 : ℕ)^17*50000000000000^13 ≤ 12395576256841^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442033847 10000000000 12395576256841 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5923296331/10000000000 : ℝ), (-430254231/1250000000 : ℝ), (3442033847/10000000000 : ℝ)] ![(78777648363/156250000000 : ℝ), (247911525231/1000000000000 : ℝ), (12395576256841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5923296331/10000000000 : ℝ)|^17 ≤ (78777648363/156250000000 : ℝ)^13
        have hw : |(5923296331/10000000000 : ℝ)|=(5923296331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430254231/1250000000 : ℝ)|^17 ≤ (247911525231/1000000000000 : ℝ)^13
        have hw : |(-430254231/1250000000 : ℝ)|=(430254231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3442033847/10000000000 : ℝ)|^17 ≤ (12395576256841/50000000000000 : ℝ)^13
        have hw : |(3442033847/10000000000 : ℝ)|=(3442033847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304042_s0_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (0 : ℝ)*x 1 + (-1 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1 : ℝ)^17 ≤ (1 : ℝ)^13 := by
    have hnat : (1 : ℕ)^17*1^13 ≤ 1^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1 : ℝ)|^17 ≤ (1 : ℝ)^13
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304042_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5923296331/10000000000 : ℝ)*x 0 + (-430254231/1250000000 : ℝ)*x 1 + (-3442033847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5923296331/10000000000 : ℝ)^17 ≤ (78777648363/156250000000 : ℝ)^13 := by
    have hnat : (5923296331 : ℕ)^17*156250000000^13 ≤ 78777648363^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923296331 10000000000 78777648363 156250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430254231/1250000000 : ℝ)^17 ≤ (247911525231/1000000000000 : ℝ)^13 := by
    have hnat : (430254231 : ℕ)^17*1000000000000^13 ≤ 247911525231^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430254231 1250000000 247911525231 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3442033847/10000000000 : ℝ)^17 ≤ (12395576256841/50000000000000 : ℝ)^13 := by
    have hnat : (3442033847 : ℕ)^17*50000000000000^13 ≤ 12395576256841^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442033847 10000000000 12395576256841 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5923296331/10000000000 : ℝ), (-430254231/1250000000 : ℝ), (-3442033847/10000000000 : ℝ)] ![(78777648363/156250000000 : ℝ), (247911525231/1000000000000 : ℝ), (12395576256841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5923296331/10000000000 : ℝ)|^17 ≤ (78777648363/156250000000 : ℝ)^13
        have hw : |(5923296331/10000000000 : ℝ)|=(5923296331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430254231/1250000000 : ℝ)|^17 ≤ (247911525231/1000000000000 : ℝ)^13
        have hw : |(-430254231/1250000000 : ℝ)|=(430254231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3442033847/10000000000 : ℝ)|^17 ≤ (12395576256841/50000000000000 : ℝ)^13
        have hw : |(-3442033847/10000000000 : ℝ)|=(3442033847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304042 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1526747987/5000000000 : ℝ)*X 0 0+(-4905535447/10000000000 : ℝ)*X 0 1+(-1226383861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304042_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1526747987/5000000000 : ℝ)*X 1 0+(4905535447/10000000000 : ℝ)*X 1 1+(-1226383861/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304042_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5923296331/10000000000 : ℝ)*X 2 0+(-430254231/1250000000 : ℝ)*X 2 1+(3442033847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304042_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_5 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304042_s0_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5923296331/10000000000 : ℝ)*X 0 0+(-430254231/1250000000 : ℝ)*X 0 1+(-3442033847/10000000000 : ℝ)*X 0 2+(5923296331/10000000000 : ℝ)*X 1 0+(-430254231/1250000000 : ℝ)*X 1 1+(-3442033847/10000000000 : ℝ)*X 1 2+(5923296331/10000000000 : ℝ)*X 2 0+(-430254231/1250000000 : ℝ)*X 2 1+(-3442033847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304042_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-1521852801853855596250816581/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23845040261/1000000000000 : ℝ)*(base5) + (8127/1000000000000 : ℝ)*(base12) + (196553140399/1000000000000 : ℝ)*(base39) + (196553131931/1000000000000 : ℝ)*(base40) + (11747/1000000000000 : ℝ)*(base44) + (8443/1000000000000 : ℝ)*(base54) + (2071582023/125000000000 : ℝ)*(base60) + (18959/12500 : ℝ)*(major_s0_0) + (1516719988253/1000000000000 : ℝ)*(major_s0_1) + (103272084019/62500000000 : ℝ)*(major_s0_2) + (2029137061007/1000000000000 : ℝ)*(sp_s0_0) + (507284264347/250000000000 : ℝ)*(sp_s0_1) + (256622762619/125000000000 : ℝ)*(sp_s0_2) + (33908338187/250000000000 : ℝ)*(sp_s0_5) + (976154939549/1000000000000 : ℝ)*(sp_s0_6) + (1014568534567/500000000000 : ℝ)*(f.sum) + (377948611048057/2000000000000000000000000000 : ℝ)*base63 + (461148024889/3125000000000000000000000 : ℝ)*base65 + (12665679874511/100000000000000000000000000 : ℝ)*base67 + (11416798393933/125000000000000000000000000 : ℝ)*base69 + (59263071653/6250000000000000000000000 : ℝ)*base71 + (458577571/400000000000000000000 : ℝ)*base73 + (465428875454871/2000000000000000000000000000 : ℝ)*base74 + (369409081/1250000000000000000000 : ℝ)*base77 + (23542775354511/100000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base91 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p004_b022 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=41 ∨ c=42 := by omega
  rcases hc with rfl|rfl
  · exact collision_c304041 p hpa (by linarith only [hpb]) X hX
  · exact collision_c304042 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p004_b022 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
