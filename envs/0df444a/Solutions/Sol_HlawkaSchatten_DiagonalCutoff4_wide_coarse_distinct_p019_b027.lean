-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:23.047855+00:00
-- url     : https://prove2.me/submissions/9532b860-6a35-4d76-b721-9060ab636cfd

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
theorem collision_support_c319048_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-75170583/312500000 : ℝ)*x 0 + (1202729313/5000000000 : ℝ)*x 1 + (-3587628553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75170583/312500000 : ℝ)^81 ≤ (16938594801973/100000000000000 : ℝ)^65 := by
    have hnat : (75170583 : ℕ)^81*100000000000000^65 ≤ 16938594801973^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75170583 312500000 16938594801973 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1202729313/5000000000 : ℝ)^81 ≤ (16938594538721/100000000000000 : ℝ)^65 := by
    have hnat : (1202729313 : ℕ)^81*100000000000000^65 ≤ 16938594538721^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202729313 5000000000 16938594538721 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3587628553/5000000000 : ℝ)^81 ≤ (66122810644721/100000000000000 : ℝ)^65 := by
    have hnat : (3587628553 : ℕ)^81*100000000000000^65 ≤ 66122810644721^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3587628553 5000000000 66122810644721 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75170583/312500000 : ℝ), (1202729313/5000000000 : ℝ), (-3587628553/5000000000 : ℝ)] ![(16938594801973/100000000000000 : ℝ), (16938594538721/100000000000000 : ℝ), (66122810644721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75170583/312500000 : ℝ)|^81 ≤ (16938594801973/100000000000000 : ℝ)^65
        have hw : |(-75170583/312500000 : ℝ)|=(75170583/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1202729313/5000000000 : ℝ)|^81 ≤ (16938594538721/100000000000000 : ℝ)^65
        have hw : |(1202729313/5000000000 : ℝ)|=(1202729313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3587628553/5000000000 : ℝ)|^81 ≤ (66122810644721/100000000000000 : ℝ)^65
        have hw : |(-3587628553/5000000000 : ℝ)|=(3587628553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3284599881/10000000000 : ℝ)*x 0 + (-20528749/62500000 : ℝ)*x 1 + (-5738723073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3284599881/10000000000 : ℝ)^81 ≤ (1560783952607/6250000000000 : ℝ)^65 := by
    have hnat : (3284599881 : ℕ)^81*6250000000000^65 ≤ 1560783952607^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3284599881 10000000000 1560783952607 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20528749/62500000 : ℝ)^81 ≤ (12486271426631/50000000000000 : ℝ)^65 := by
    have hnat : (20528749 : ℕ)^81*50000000000000^65 ≤ 12486271426631^65*62500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20528749 62500000 12486271426631 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5738723073/10000000000 : ℝ)^81 ≤ (312843211809/625000000000 : ℝ)^65 := by
    have hnat : (5738723073 : ℕ)^81*625000000000^65 ≤ 312843211809^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5738723073 10000000000 312843211809 625000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3284599881/10000000000 : ℝ), (-20528749/62500000 : ℝ), (-5738723073/10000000000 : ℝ)] ![(1560783952607/6250000000000 : ℝ), (12486271426631/50000000000000 : ℝ), (312843211809/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3284599881/10000000000 : ℝ)|^81 ≤ (1560783952607/6250000000000 : ℝ)^65
        have hw : |(3284599881/10000000000 : ℝ)|=(3284599881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20528749/62500000 : ℝ)|^81 ≤ (12486271426631/50000000000000 : ℝ)^65
        have hw : |(-20528749/62500000 : ℝ)|=(20528749/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5738723073/10000000000 : ℝ)|^81 ≤ (312843211809/625000000000 : ℝ)^65
        have hw : |(-5738723073/10000000000 : ℝ)|=(5738723073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1304349359/10000000000 : ℝ)*x 0 + (831360057/10000000000 : ℝ)*x 1 + (-71931983/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1304349359/10000000000 : ℝ)^81 ≤ (7900321087949/100000000000000 : ℝ)^65 := by
    have hnat : (1304349359 : ℕ)^81*100000000000000^65 ≤ 7900321087949^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304349359 10000000000 7900321087949 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831360057/10000000000 : ℝ)^81 ≤ (35211224719/781250000000 : ℝ)^65 := by
    have hnat : (831360057 : ℕ)^81*781250000000^65 ≤ 35211224719^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831360057 10000000000 35211224719 781250000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71931983/80000000 : ℝ)^81 ≤ (1094908026623/1250000000000 : ℝ)^65 := by
    have hnat : (71931983 : ℕ)^81*1250000000000^65 ≤ 1094908026623^65*80000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71931983 80000000 1094908026623 1250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1304349359/10000000000 : ℝ), (831360057/10000000000 : ℝ), (-71931983/80000000 : ℝ)] ![(7900321087949/100000000000000 : ℝ), (35211224719/781250000000 : ℝ), (1094908026623/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1304349359/10000000000 : ℝ)|^81 ≤ (7900321087949/100000000000000 : ℝ)^65
        have hw : |(-1304349359/10000000000 : ℝ)|=(1304349359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831360057/10000000000 : ℝ)|^81 ≤ (35211224719/781250000000 : ℝ)^65
        have hw : |(831360057/10000000000 : ℝ)|=(831360057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71931983/80000000 : ℝ)|^81 ≤ (1094908026623/1250000000000 : ℝ)^65
        have hw : |(-71931983/80000000 : ℝ)|=(71931983/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (546677619/2000000000 : ℝ)*x 0 + (-1864491183/10000000000 : ℝ)*x 1 + (-146429019/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546677619/2000000000 : ℝ)^81 ≤ (2482865361489/12500000000000 : ℝ)^65 := by
    have hnat : (546677619 : ℕ)^81*12500000000000^65 ≤ 2482865361489^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546677619 2000000000 2482865361489 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864491183/10000000000 : ℝ)^81 ≤ (3082804351269/25000000000000 : ℝ)^65 := by
    have hnat : (1864491183 : ℕ)^81*25000000000000^65 ≤ 3082804351269^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864491183 10000000000 3082804351269 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146429019/200000000 : ℝ)^81 ≤ (67805859690097/100000000000000 : ℝ)^65 := by
    have hnat : (146429019 : ℕ)^81*100000000000000^65 ≤ 67805859690097^65*200000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146429019 200000000 67805859690097 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546677619/2000000000 : ℝ), (-1864491183/10000000000 : ℝ), (-146429019/200000000 : ℝ)] ![(2482865361489/12500000000000 : ℝ), (3082804351269/25000000000000 : ℝ), (67805859690097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546677619/2000000000 : ℝ)|^81 ≤ (2482865361489/12500000000000 : ℝ)^65
        have hw : |(546677619/2000000000 : ℝ)|=(546677619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1864491183/10000000000 : ℝ)|^81 ≤ (3082804351269/25000000000000 : ℝ)^65
        have hw : |(-1864491183/10000000000 : ℝ)|=(1864491183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-146429019/200000000 : ℝ)|^81 ≤ (67805859690097/100000000000000 : ℝ)^65
        have hw : |(-146429019/200000000 : ℝ)|=(146429019/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3619532321/10000000000 : ℝ)*x 0 + (7641173021/10000000000 : ℝ)*x 1 + (47247179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3619532321/10000000000 : ℝ)^81 ≤ (5636935429249/20000000000000 : ℝ)^65 := by
    have hnat : (3619532321 : ℕ)^81*20000000000000^65 ≤ 5636935429249^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619532321 10000000000 5636935429249 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7641173021/10000000000 : ℝ)^81 ≤ (7151537603211/10000000000000 : ℝ)^65 := by
    have hnat : (7641173021 : ℕ)^81*10000000000000^65 ≤ 7151537603211^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7641173021 10000000000 7151537603211 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47247179/5000000000 : ℝ)^81 ≤ (14997340549/5000000000000 : ℝ)^65 := by
    have hnat : (47247179 : ℕ)^81*5000000000000^65 ≤ 14997340549^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47247179 5000000000 14997340549 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3619532321/10000000000 : ℝ), (7641173021/10000000000 : ℝ), (47247179/5000000000 : ℝ)] ![(5636935429249/20000000000000 : ℝ), (7151537603211/10000000000000 : ℝ), (14997340549/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3619532321/10000000000 : ℝ)|^81 ≤ (5636935429249/20000000000000 : ℝ)^65
        have hw : |(3619532321/10000000000 : ℝ)|=(3619532321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7641173021/10000000000 : ℝ)|^81 ≤ (7151537603211/10000000000000 : ℝ)^65
        have hw : |(7641173021/10000000000 : ℝ)|=(7641173021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47247179/5000000000 : ℝ)|^81 ≤ (14997340549/5000000000000 : ℝ)^65
        have hw : |(47247179/5000000000 : ℝ)|=(47247179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3540980819/10000000000 : ℝ)*x 0 + (7641173021/10000000000 : ℝ)*x 1 + (-260262711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3540980819/10000000000 : ℝ)^81 ≤ (6856123257083/25000000000000 : ℝ)^65 := by
    have hnat : (3540980819 : ℕ)^81*25000000000000^65 ≤ 6856123257083^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3540980819 10000000000 6856123257083 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7641173021/10000000000 : ℝ)^81 ≤ (7151537603211/10000000000000 : ℝ)^65 := by
    have hnat : (7641173021 : ℕ)^81*10000000000000^65 ≤ 7151537603211^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7641173021 10000000000 7151537603211 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260262711/10000000000 : ℝ)^81 ≤ (1060130931181/100000000000000 : ℝ)^65 := by
    have hnat : (260262711 : ℕ)^81*100000000000000^65 ≤ 1060130931181^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260262711 10000000000 1060130931181 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3540980819/10000000000 : ℝ), (7641173021/10000000000 : ℝ), (-260262711/10000000000 : ℝ)] ![(6856123257083/25000000000000 : ℝ), (7151537603211/10000000000000 : ℝ), (1060130931181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3540980819/10000000000 : ℝ)|^81 ≤ (6856123257083/25000000000000 : ℝ)^65
        have hw : |(3540980819/10000000000 : ℝ)|=(3540980819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7641173021/10000000000 : ℝ)|^81 ≤ (7151537603211/10000000000000 : ℝ)^65
        have hw : |(7641173021/10000000000 : ℝ)|=(7641173021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260262711/10000000000 : ℝ)|^81 ≤ (1060130931181/100000000000000 : ℝ)^65
        have hw : |(-260262711/10000000000 : ℝ)|=(260262711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-865949369/10000000000 : ℝ)*x 0 + (161262891/1250000000 : ℝ)*x 1 + (-8980995447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865949369/10000000000 : ℝ)^81 ≤ (592737228869/12500000000000 : ℝ)^65 := by
    have hnat : (865949369 : ℕ)^81*12500000000000^65 ≤ 592737228869^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865949369 10000000000 592737228869 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161262891/1250000000 : ℝ)^81 ≤ (1558587562403/20000000000000 : ℝ)^65 := by
    have hnat : (161262891 : ℕ)^81*20000000000000^65 ≤ 1558587562403^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161262891 1250000000 1558587562403 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8980995447/10000000000 : ℝ)^81 ≤ (87465164347639/100000000000000 : ℝ)^65 := by
    have hnat : (8980995447 : ℕ)^81*100000000000000^65 ≤ 87465164347639^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8980995447 10000000000 87465164347639 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-865949369/10000000000 : ℝ), (161262891/1250000000 : ℝ), (-8980995447/10000000000 : ℝ)] ![(592737228869/12500000000000 : ℝ), (1558587562403/20000000000000 : ℝ), (87465164347639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-865949369/10000000000 : ℝ)|^81 ≤ (592737228869/12500000000000 : ℝ)^65
        have hw : |(-865949369/10000000000 : ℝ)|=(865949369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161262891/1250000000 : ℝ)|^81 ≤ (1558587562403/20000000000000 : ℝ)^65
        have hw : |(161262891/1250000000 : ℝ)|=(161262891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8980995447/10000000000 : ℝ)|^81 ≤ (87465164347639/100000000000000 : ℝ)^65
        have hw : |(-8980995447/10000000000 : ℝ)|=(8980995447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (362788717/2000000000 : ℝ)*x 0 + (-687244931/2500000000 : ℝ)*x 1 + (-3672587601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362788717/2000000000 : ℝ)^81 ≤ (2979004613201/25000000000000 : ℝ)^65 := by
    have hnat : (362788717 : ℕ)^81*25000000000000^65 ≤ 2979004613201^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362788717 2000000000 2979004613201 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687244931/2500000000 : ℝ)^81 ≤ (10002106110941/50000000000000 : ℝ)^65 := by
    have hnat : (687244931 : ℕ)^81*50000000000000^65 ≤ 10002106110941^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687244931 2500000000 10002106110941 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3672587601/5000000000 : ℝ)^81 ≤ (108927630899/160000000000 : ℝ)^65 := by
    have hnat : (3672587601 : ℕ)^81*160000000000^65 ≤ 108927630899^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672587601 5000000000 108927630899 160000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(362788717/2000000000 : ℝ), (-687244931/2500000000 : ℝ), (-3672587601/5000000000 : ℝ)] ![(2979004613201/25000000000000 : ℝ), (10002106110941/50000000000000 : ℝ), (108927630899/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(362788717/2000000000 : ℝ)|^81 ≤ (2979004613201/25000000000000 : ℝ)^65
        have hw : |(362788717/2000000000 : ℝ)|=(362788717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-687244931/2500000000 : ℝ)|^81 ≤ (10002106110941/50000000000000 : ℝ)^65
        have hw : |(-687244931/2500000000 : ℝ)|=(687244931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3672587601/5000000000 : ℝ)|^81 ≤ (108927630899/160000000000 : ℝ)^65
        have hw : |(-3672587601/5000000000 : ℝ)|=(3672587601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3827593869/5000000000 : ℝ)*x 0 + (448721739/1250000000 : ℝ)*x 1 + (62483453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3827593869/5000000000 : ℝ)^81 ≤ (17919716712579/25000000000000 : ℝ)^65 := by
    have hnat : (3827593869 : ℕ)^81*25000000000000^65 ≤ 17919716712579^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3827593869 5000000000 17919716712579 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448721739/1250000000 : ℝ)^81 ≤ (13948103331343/50000000000000 : ℝ)^65 := by
    have hnat : (448721739 : ℕ)^81*50000000000000^65 ≤ 13948103331343^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448721739 1250000000 13948103331343 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62483453/5000000000 : ℝ)^81 ≤ (212463237683/50000000000000 : ℝ)^65 := by
    have hnat : (62483453 : ℕ)^81*50000000000000^65 ≤ 212463237683^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62483453 5000000000 212463237683 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3827593869/5000000000 : ℝ), (448721739/1250000000 : ℝ), (62483453/5000000000 : ℝ)] ![(17919716712579/25000000000000 : ℝ), (13948103331343/50000000000000 : ℝ), (212463237683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3827593869/5000000000 : ℝ)|^81 ≤ (17919716712579/25000000000000 : ℝ)^65
        have hw : |(3827593869/5000000000 : ℝ)|=(3827593869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448721739/1250000000 : ℝ)|^81 ≤ (13948103331343/50000000000000 : ℝ)^65
        have hw : |(448721739/1250000000 : ℝ)|=(448721739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62483453/5000000000 : ℝ)|^81 ≤ (212463237683/50000000000000 : ℝ)^65
        have hw : |(62483453/5000000000 : ℝ)|=(62483453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1905880231/2500000000 : ℝ)*x 0 + (448721739/1250000000 : ℝ)*x 1 + (-206430623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905880231/2500000000 : ℝ)^81 ≤ (17827389456229/25000000000000 : ℝ)^65 := by
    have hnat : (1905880231 : ℕ)^81*25000000000000^65 ≤ 17827389456229^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905880231 2500000000 17827389456229 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448721739/1250000000 : ℝ)^81 ≤ (13948103331343/50000000000000 : ℝ)^65 := by
    have hnat : (448721739 : ℕ)^81*50000000000000^65 ≤ 13948103331343^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448721739 1250000000 13948103331343 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206430623/10000000000 : ℝ)^81 ≤ (794235494881/100000000000000 : ℝ)^65 := by
    have hnat : (206430623 : ℕ)^81*100000000000000^65 ≤ 794235494881^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206430623 10000000000 794235494881 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1905880231/2500000000 : ℝ), (448721739/1250000000 : ℝ), (-206430623/10000000000 : ℝ)] ![(17827389456229/25000000000000 : ℝ), (13948103331343/50000000000000 : ℝ), (794235494881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1905880231/2500000000 : ℝ)|^81 ≤ (17827389456229/25000000000000 : ℝ)^65
        have hw : |(1905880231/2500000000 : ℝ)|=(1905880231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448721739/1250000000 : ℝ)|^81 ≤ (13948103331343/50000000000000 : ℝ)^65
        have hw : |(448721739/1250000000 : ℝ)|=(448721739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206430623/10000000000 : ℝ)|^81 ≤ (794235494881/100000000000000 : ℝ)^65
        have hw : |(-206430623/10000000000 : ℝ)|=(206430623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844586383/5000000000 : ℝ)*x 0 + (324821027/2500000000 : ℝ)*x 1 + (-3463137079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844586383/5000000000 : ℝ)^81 ≤ (7215507938407/25000000000000 : ℝ)^65 := by
    have hnat : (1844586383 : ℕ)^81*25000000000000^65 ≤ 7215507938407^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844586383 5000000000 7215507938407 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324821027/2500000000 : ℝ)^81 ≤ (3931053846529/50000000000000 : ℝ)^65 := by
    have hnat : (324821027 : ℕ)^81*50000000000000^65 ≤ 3931053846529^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324821027 2500000000 3931053846529 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3463137079/5000000000 : ℝ)^81 ≤ (63275860540453/100000000000000 : ℝ)^65 := by
    have hnat : (3463137079 : ℕ)^81*100000000000000^65 ≤ 63275860540453^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3463137079 5000000000 63275860540453 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844586383/5000000000 : ℝ), (324821027/2500000000 : ℝ), (-3463137079/5000000000 : ℝ)] ![(7215507938407/25000000000000 : ℝ), (3931053846529/50000000000000 : ℝ), (63275860540453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844586383/5000000000 : ℝ)|^81 ≤ (7215507938407/25000000000000 : ℝ)^65
        have hw : |(-1844586383/5000000000 : ℝ)|=(1844586383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324821027/2500000000 : ℝ)|^81 ≤ (3931053846529/50000000000000 : ℝ)^65
        have hw : |(324821027/2500000000 : ℝ)|=(324821027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3463137079/5000000000 : ℝ)|^81 ≤ (63275860540453/100000000000000 : ℝ)^65
        have hw : |(-3463137079/5000000000 : ℝ)|=(3463137079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2178608471/10000000000 : ℝ)*x 0 + (-2284248649/5000000000 : ℝ)*x 1 + (-5489046151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178608471/10000000000 : ℝ)^81 ≤ (3742910636409/25000000000000 : ℝ)^65 := by
    have hnat : (2178608471 : ℕ)^81*25000000000000^65 ≤ 3742910636409^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178608471 10000000000 3742910636409 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284248649/5000000000 : ℝ)^81 ≤ (1506902907271/4000000000000 : ℝ)^65 := by
    have hnat : (2284248649 : ℕ)^81*4000000000000^65 ≤ 1506902907271^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284248649 5000000000 1506902907271 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489046151/10000000000 : ℝ)^81 ≤ (23677892377749/50000000000000 : ℝ)^65 := by
    have hnat : (5489046151 : ℕ)^81*50000000000000^65 ≤ 23677892377749^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489046151 10000000000 23677892377749 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178608471/10000000000 : ℝ), (-2284248649/5000000000 : ℝ), (-5489046151/10000000000 : ℝ)] ![(3742910636409/25000000000000 : ℝ), (1506902907271/4000000000000 : ℝ), (23677892377749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178608471/10000000000 : ℝ)|^81 ≤ (3742910636409/25000000000000 : ℝ)^65
        have hw : |(2178608471/10000000000 : ℝ)|=(2178608471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284248649/5000000000 : ℝ)|^81 ≤ (1506902907271/4000000000000 : ℝ)^65
        have hw : |(-2284248649/5000000000 : ℝ)|=(2284248649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5489046151/10000000000 : ℝ)|^81 ≤ (23677892377749/50000000000000 : ℝ)^65
        have hw : |(-5489046151/10000000000 : ℝ)|=(5489046151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (71582993/125000000 : ℝ)*x 0 + (5726639353/10000000000 : ℝ)*x 1 + (13748547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71582993/125000000 : ℝ)^81 ≤ (1560112714003/3125000000000 : ℝ)^65 := by
    have hnat : (71582993 : ℕ)^81*3125000000000^65 ≤ 1560112714003^65*125000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71582993 125000000 1560112714003 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5726639353/10000000000 : ℝ)^81 ≤ (9984721180591/20000000000000 : ℝ)^65 := by
    have hnat : (5726639353 : ℕ)^81*20000000000000^65 ≤ 9984721180591^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5726639353 10000000000 9984721180591 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13748547/2500000000 : ℝ)^81 ≤ (76393619299/50000000000000 : ℝ)^65 := by
    have hnat : (13748547 : ℕ)^81*50000000000000^65 ≤ 76393619299^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13748547 2500000000 76393619299 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71582993/125000000 : ℝ), (5726639353/10000000000 : ℝ), (13748547/2500000000 : ℝ)] ![(1560112714003/3125000000000 : ℝ), (9984721180591/20000000000000 : ℝ), (76393619299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71582993/125000000 : ℝ)|^81 ≤ (1560112714003/3125000000000 : ℝ)^65
        have hw : |(71582993/125000000 : ℝ)|=(71582993/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5726639353/10000000000 : ℝ)|^81 ≤ (9984721180591/20000000000000 : ℝ)^65
        have hw : |(5726639353/10000000000 : ℝ)|=(5726639353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13748547/2500000000 : ℝ)|^81 ≤ (76393619299/50000000000000 : ℝ)^65
        have hw : |(13748547/2500000000 : ℝ)|=(13748547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1466386369/5000000000 : ℝ)*x 0 + (586428057/2000000000 : ℝ)*x 1 + (-1584203713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1466386369/5000000000 : ℝ)^81 ≤ (21684376660639/100000000000000 : ℝ)^65 := by
    have hnat : (1466386369 : ℕ)^81*100000000000000^65 ≤ 21684376660639^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466386369 5000000000 21684376660639 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586428057/2000000000 : ℝ)^81 ≤ (10839274750451/50000000000000 : ℝ)^65 := by
    have hnat : (586428057 : ℕ)^81*50000000000000^65 ≤ 10839274750451^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586428057 2000000000 10839274750451 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584203713/2500000000 : ℝ)^81 ≤ (28318536910867/50000000000000 : ℝ)^65 := by
    have hnat : (1584203713 : ℕ)^81*50000000000000^65 ≤ 28318536910867^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584203713 2500000000 28318536910867 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1466386369/5000000000 : ℝ), (586428057/2000000000 : ℝ), (-1584203713/2500000000 : ℝ)] ![(21684376660639/100000000000000 : ℝ), (10839274750451/50000000000000 : ℝ), (28318536910867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1466386369/5000000000 : ℝ)|^81 ≤ (21684376660639/100000000000000 : ℝ)^65
        have hw : |(-1466386369/5000000000 : ℝ)|=(1466386369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586428057/2000000000 : ℝ)|^81 ≤ (10839274750451/50000000000000 : ℝ)^65
        have hw : |(586428057/2000000000 : ℝ)|=(586428057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1584203713/2500000000 : ℝ)|^81 ≤ (28318536910867/50000000000000 : ℝ)^65
        have hw : |(-1584203713/2500000000 : ℝ)|=(1584203713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3633957513/10000000000 : ℝ)*x 0 + (-3633173849/10000000000 : ℝ)*x 1 + (-2556999373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3633957513/10000000000 : ℝ)^81 ≤ (5664944366153/20000000000000 : ℝ)^65 := by
    have hnat : (3633957513 : ℕ)^81*20000000000000^65 ≤ 5664944366153^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633957513 10000000000 5664944366153 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3633173849/10000000000 : ℝ)^81 ≤ (7079277558209/25000000000000 : ℝ)^65 := by
    have hnat : (3633173849 : ℕ)^81*25000000000000^65 ≤ 7079277558209^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633173849 10000000000 7079277558209 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2556999373/5000000000 : ℝ)^81 ≤ (10839541979253/25000000000000 : ℝ)^65 := by
    have hnat : (2556999373 : ℕ)^81*25000000000000^65 ≤ 10839541979253^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556999373 5000000000 10839541979253 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3633957513/10000000000 : ℝ), (-3633173849/10000000000 : ℝ), (-2556999373/5000000000 : ℝ)] ![(5664944366153/20000000000000 : ℝ), (7079277558209/25000000000000 : ℝ), (10839541979253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3633957513/10000000000 : ℝ)|^81 ≤ (5664944366153/20000000000000 : ℝ)^65
        have hw : |(3633957513/10000000000 : ℝ)|=(3633957513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3633173849/10000000000 : ℝ)|^81 ≤ (7079277558209/25000000000000 : ℝ)^65
        have hw : |(-3633173849/10000000000 : ℝ)|=(3633173849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2556999373/5000000000 : ℝ)|^81 ≤ (10839541979253/25000000000000 : ℝ)^65
        have hw : |(-2556999373/5000000000 : ℝ)|=(2556999373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5302073163/10000000000 : ℝ)*x 0 + (132578003/250000000 : ℝ)*x 1 + (1484259607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302073163/10000000000 : ℝ)^81 ≤ (2834633966411/6250000000000 : ℝ)^65 := by
    have hnat : (5302073163 : ℕ)^81*6250000000000^65 ≤ 2834633966411^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302073163 10000000000 2834633966411 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132578003/250000000 : ℝ)^81 ≤ (2835331495513/6250000000000 : ℝ)^65 := by
    have hnat : (132578003 : ℕ)^81*6250000000000^65 ≤ 2835331495513^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132578003 250000000 2835331495513 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1484259607/10000000000 : ℝ)^81 ≤ (2320138148469/25000000000000 : ℝ)^65 := by
    have hnat : (1484259607 : ℕ)^81*25000000000000^65 ≤ 2320138148469^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484259607 10000000000 2320138148469 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302073163/10000000000 : ℝ), (132578003/250000000 : ℝ), (1484259607/10000000000 : ℝ)] ![(2834633966411/6250000000000 : ℝ), (2835331495513/6250000000000 : ℝ), (2320138148469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302073163/10000000000 : ℝ)|^81 ≤ (2834633966411/6250000000000 : ℝ)^65
        have hw : |(5302073163/10000000000 : ℝ)|=(5302073163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132578003/250000000 : ℝ)|^81 ≤ (2835331495513/6250000000000 : ℝ)^65
        have hw : |(132578003/250000000 : ℝ)|=(132578003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1484259607/10000000000 : ℝ)|^81 ≤ (2320138148469/25000000000000 : ℝ)^65
        have hw : |(1484259607/10000000000 : ℝ)|=(1484259607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319048_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2519357839/5000000000 : ℝ)*x 0 + (629963829/1250000000 : ℝ)*x 1 + (-541421939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2519357839/5000000000 : ℝ)^81 ≤ (2660264120773/6250000000000 : ℝ)^65 := by
    have hnat : (2519357839 : ℕ)^81*6250000000000^65 ≤ 2660264120773^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519357839 5000000000 2660264120773 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629963829/1250000000 : ℝ)^81 ≤ (2128734993647/5000000000000 : ℝ)^65 := by
    have hnat : (629963829 : ℕ)^81*5000000000000^65 ≤ 2128734993647^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629963829 1250000000 2128734993647 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541421939/2500000000 : ℝ)^81 ≤ (14861074183947/100000000000000 : ℝ)^65 := by
    have hnat : (541421939 : ℕ)^81*100000000000000^65 ≤ 14861074183947^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541421939 2500000000 14861074183947 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2519357839/5000000000 : ℝ), (629963829/1250000000 : ℝ), (-541421939/2500000000 : ℝ)] ![(2660264120773/6250000000000 : ℝ), (2128734993647/5000000000000 : ℝ), (14861074183947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2519357839/5000000000 : ℝ)|^81 ≤ (2660264120773/6250000000000 : ℝ)^65
        have hw : |(2519357839/5000000000 : ℝ)|=(2519357839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629963829/1250000000 : ℝ)|^81 ≤ (2128734993647/5000000000000 : ℝ)^65
        have hw : |(629963829/1250000000 : ℝ)|=(629963829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-541421939/2500000000 : ℝ)|^81 ≤ (14861074183947/100000000000000 : ℝ)^65
        have hw : |(-541421939/2500000000 : ℝ)|=(541421939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319048 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-75170583/312500000 : ℝ)*X 0 0+(1202729313/5000000000 : ℝ)*X 0 1+(-3587628553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3284599881/10000000000 : ℝ)*X 1 0+(-20528749/62500000 : ℝ)*X 1 1+(-5738723073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1304349359/10000000000 : ℝ)*X 0 0+(831360057/10000000000 : ℝ)*X 0 1+(-71931983/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((546677619/2000000000 : ℝ)*X 1 0+(-1864491183/10000000000 : ℝ)*X 1 1+(-146429019/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3619532321/10000000000 : ℝ)*X 2 0+(7641173021/10000000000 : ℝ)*X 2 1+(47247179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3540980819/10000000000 : ℝ)*X 0 0+(7641173021/10000000000 : ℝ)*X 0 1+(-260262711/10000000000 : ℝ)*X 0 2+(3540980819/10000000000 : ℝ)*X 1 0+(7641173021/10000000000 : ℝ)*X 1 1+(-260262711/10000000000 : ℝ)*X 1 2+(3540980819/10000000000 : ℝ)*X 2 0+(7641173021/10000000000 : ℝ)*X 2 1+(-260262711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-865949369/10000000000 : ℝ)*X 0 0+(161262891/1250000000 : ℝ)*X 0 1+(-8980995447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((362788717/2000000000 : ℝ)*X 1 0+(-687244931/2500000000 : ℝ)*X 1 1+(-3672587601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3827593869/5000000000 : ℝ)*X 2 0+(448721739/1250000000 : ℝ)*X 2 1+(62483453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1905880231/2500000000 : ℝ)*X 0 0+(448721739/1250000000 : ℝ)*X 0 1+(-206430623/10000000000 : ℝ)*X 0 2+(1905880231/2500000000 : ℝ)*X 1 0+(448721739/1250000000 : ℝ)*X 1 1+(-206430623/10000000000 : ℝ)*X 1 2+(1905880231/2500000000 : ℝ)*X 2 0+(448721739/1250000000 : ℝ)*X 2 1+(-206430623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1844586383/5000000000 : ℝ)*X 0 0+(324821027/2500000000 : ℝ)*X 0 1+(-3463137079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2178608471/10000000000 : ℝ)*X 1 0+(-2284248649/5000000000 : ℝ)*X 1 1+(-5489046151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((71582993/125000000 : ℝ)*X 2 0+(5726639353/10000000000 : ℝ)*X 2 1+(13748547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6901/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6901/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (111737798946225663/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (205137041151/200000000000 : ℝ)*(base5) + (211046386161/250000000000 : ℝ)*(base7) + (9374712737/1000000000000 : ℝ)*(base39) + (880351140851/1000000000000 : ℝ)*(base59) + (1910564255827/1000000000000 : ℝ)*(major_s0_0) + (1910564255827/1000000000000 : ℝ)*(major_s0_1) + (1910564255827/1000000000000 : ℝ)*(major_s0_2) + (3904863/1000000000000 : ℝ)*(sp_s0_0) + (5408033/1000000000000 : ℝ)*(sp_s0_1) + (1154703931603/500000000000 : ℝ)*(sp_s0_7) + (1154746724207/500000000000 : ℝ)*(sp_s0_8) + (1667592031101/500000000000 : ℝ)*(sp_s0_9) + (850713298697/1000000000000 : ℝ)*(sp_s0_13) + (43544189/500000000000 : ℝ)*(sp_s0_14) + (16128327497/15625000000 : ℝ)*(f.failure) + (2309498856447/1000000000000 : ℝ)*(f.sum) + (491269721/10000000000000000000000 : ℝ)*base63 + (401762497901131/10000000000000000000000000000 : ℝ)*base65 + (3755080240098869/10000000000000000000000000000 : ℝ)*base66 + (2917274102991617/10000000000000000000000000000 : ℝ)*base69 + (871262002545243/5000000000000000000000000000 : ℝ)*base70 + (430997222901131/10000000000000000000000000000 : ℝ)*base72 + (4407433966008383/10000000000000000000000000000 : ℝ)*base75 + (6376451772008383/10000000000000000000000000000 : ℝ)*base77 + (3023931251/10000000000000000000000 : ℝ)*base79 + (61/3125000000000000 : ℝ)*base87 + (61/3125000000000000 : ℝ)*base89 + (61/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34461/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34461/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64192093754319291/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (154650342629/500000000000 : ℝ)*(base5) + (106850075001/125000000000 : ℝ)*(base7) + (129637/1000000000000 : ℝ)*(base39) + (163639401067/1000000000000 : ℝ)*(base59) + (47474816407/25000000000 : ℝ)*(major_s0_0) + (47474816407/25000000000 : ℝ)*(major_s0_1) + (47474816407/25000000000 : ℝ)*(major_s0_2) + (3616659/1000000000000 : ℝ)*(sp_s0_0) + (588433/125000000000 : ℝ)*(sp_s0_1) + (6134983/125000000000 : ℝ)*(sp_s0_8) + (1143287468993/500000000000 : ℝ)*(sp_s0_14) + (2286524767317/1000000000000 : ℝ)*(sp_s0_15) + (2595879239903/1000000000000 : ℝ)*(sp_s0_16) + (314292226489/200000000000 : ℝ)*(sp_s0_20) + (205192243539/200000000000 : ℝ)*(f.failure) + (457315710929/200000000000 : ℝ)*(f.sum) + (1652299021/5000000000000000000000 : ℝ)*base62 + (12784632503871/250000000000000000000000000 : ℝ)*base65 + (126185682171129/250000000000000000000000000 : ℝ)*base66 + (4566656433797/250000000000000000000000000 : ℝ)*base69 + (45418829052463/125000000000000000000000000 : ℝ)*base70 + (88662673528871/250000000000000000000000000 : ℝ)*base72 + (32000591491203/250000000000000000000000000 : ℝ)*base75 + (86553171941203/250000000000000000000000000 : ℝ)*base77 + (597213117/10000000000000000000000 : ℝ)*base79 + (3833/10000000000000000 : ℝ)*base87 + (3833/10000000000000000 : ℝ)*base89 + (3833/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-17979/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-17979/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6105523825605853590189/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (526296222661/500000000000 : ℝ)*(base5) + (40782486267/1000000000000 : ℝ)*(base7) + (2246973/500000000000 : ℝ)*(base8) + (886733/1000000000000 : ℝ)*(base15) + (235097/40000000000 : ℝ)*(base16) + (20695520583/1000000000000 : ℝ)*(base39) + (1336170641069/1000000000000 : ℝ)*(base59) + (936399762807/500000000000 : ℝ)*(major_s0_0) + (936399762807/500000000000 : ℝ)*(major_s0_1) + (936399762807/500000000000 : ℝ)*(major_s0_2) + (8141/100000000000 : ℝ)*(sp_s0_9) + (2710622596127/1000000000000 : ℝ)*(sp_s0_21) + (677655081479/250000000000 : ℝ)*(sp_s0_22) + (1881609726993/500000000000 : ℝ)*(sp_s0_23) + (202361991811/200000000000 : ℝ)*(f.failure) + (1355313545037/500000000000 : ℝ)*(f.sum) + (2027261359/5000000000000000000000 : ℝ)*base62 + (2195704501573071/5000000000000000000000000000 : ℝ)*base65 + (3392077607426929/5000000000000000000000000000 : ℝ)*base66 + (538729006133197/5000000000000000000000000000 : ℝ)*base69 + (643585309719937/2500000000000000000000000000 : ℝ)*base71 + (3159754701573071/5000000000000000000000000000 : ℝ)*base72 + (2962523550866803/5000000000000000000000000000 : ℝ)*base75 + (2124078441866803/5000000000000000000000000000 : ℝ)*base77 + (137279537/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (7383/10000000000000000 : ℝ)*base86 + (7383/10000000000000000 : ℝ)*base88 + (7383/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (6901/10000 : ℝ) ^ (79/16 : ℝ) ≤ (16018731992567012973/100000000000000000000 : ℝ) := by
    have hpowers : (6901/10000 : ℝ)^79 ≤ (16018731992567012973/100000000000000000000 : ℝ)^16 := by
      have hnat : (6901 : ℕ)^79*100000000000000000000^16 ≤ 16018731992567012973^16*10000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6901 10000 16018731992567012973 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6901/10000 : ℝ)) (X := (16018731992567012973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (116018731992567012973/100000000000000000000 : ℝ) ≤ (257637451121109/250000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (116018731992567012973/100000000000000000000 : ℝ)^16 ≤ (257637451121109/250000000000000 : ℝ)^79 := by
      have hnat : (116018731992567012973 : ℕ)^16*250000000000000^79 ≤ 257637451121109^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116018731992567012973 100000000000000000000 257637451121109 250000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (257637451121109/250000000000000 : ℝ)) (X := (116018731992567012973/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (66018731992567012973/50000000000000000000 : ℝ) ≤ (2115801852277739/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (66018731992567012973/50000000000000000000 : ℝ)^16 ≤ (2115801852277739/2000000000000000 : ℝ)^79 := by
      have hnat : (66018731992567012973 : ℕ)^16*2000000000000000^79 ≤ 2115801852277739^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66018731992567012973 50000000000000000000 2115801852277739 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2115801852277739/2000000000000000 : ℝ)) (X := (66018731992567012973/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7637451121109/172525000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(54702243308867/1380200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (6901/10000 : ℝ)) (alpha := (7637451121109/172525000000000 : ℝ)) (beta := (54702243308867/1380200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6901/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7637451121109/172525000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(54702243308867/1380200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (34461/50000 : ℝ) ^ (79/16 : ℝ) ≤ (7959063957550401387/50000000000000000000 : ℝ) := by
    have hpowers : (34461/50000 : ℝ)^79 ≤ (7959063957550401387/50000000000000000000 : ℝ)^16 := by
      have hnat : (34461 : ℕ)^79*50000000000000000000^16 ≤ 7959063957550401387^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34461 50000 7959063957550401387 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34461/50000 : ℝ)) (X := (7959063957550401387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (57959063957550401387/50000000000000000000 : ℝ) ≤ (10303687540557871/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (57959063957550401387/50000000000000000000 : ℝ)^16 ≤ (10303687540557871/10000000000000000 : ℝ)^79 := by
      have hnat : (57959063957550401387 : ℕ)^16*10000000000000000^79 ≤ 10303687540557871^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57959063957550401387 50000000000000000000 10303687540557871 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10303687540557871/10000000000000000 : ℝ)) (X := (57959063957550401387/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (32959063957550401387/25000000000000000000 : ℝ) ≤ (528787112616083/500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (32959063957550401387/25000000000000000000 : ℝ)^16 ≤ (528787112616083/500000000000000 : ℝ)^79 := by
      have hnat : (32959063957550401387 : ℕ)^16*500000000000000^79 ≤ 528787112616083^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32959063957550401387 25000000000000000000 528787112616083 500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (528787112616083/500000000000000 : ℝ)) (X := (32959063957550401387/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(101229180185957/2297400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(90684903921263/2297400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (34461/50000 : ℝ)) (alpha := (101229180185957/2297400000000000 : ℝ)) (beta := (90684903921263/2297400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34461/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(101229180185957/2297400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(90684903921263/2297400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (17979/100000 : ℝ) ^ (79/16 : ℝ) ≤ (2091244521826947/10000000000000000000 : ℝ) := by
    have hpowers : (17979/100000 : ℝ)^79 ≤ (2091244521826947/10000000000000000000 : ℝ)^16 := by
      have hnat : (17979 : ℕ)^79*10000000000000000000^16 ≤ 2091244521826947^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17979 100000 2091244521826947 10000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17979/100000 : ℝ)) (X := (2091244521826947/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10002091244521826947/10000000000000000000 : ℝ) ≤ (5000211753940771/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (10002091244521826947/10000000000000000000 : ℝ)^16 ≤ (5000211753940771/5000000000000000 : ℝ)^79 := by
      have hnat : (10002091244521826947 : ℕ)^16*5000000000000000^79 ≤ 5000211753940771^79*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002091244521826947 10000000000000000000 5000211753940771 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211753940771/5000000000000000 : ℝ)) (X := (10002091244521826947/10000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5002091244521826947/5000000000000000000 : ℝ) ≤ (1000084694515527/1000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (5002091244521826947/5000000000000000000 : ℝ)^16 ≤ (1000084694515527/1000000000000000 : ℝ)^79 := by
      have hnat : (5002091244521826947 : ℕ)^16*1000000000000000^79 ≤ 1000084694515527^79*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002091244521826947 5000000000000000000 1000084694515527 1000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000084694515527/1000000000000000 : ℝ)) (X := (5002091244521826947/5000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(211753940771/898950000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3308103701/14046093750000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (17979/100000 : ℝ)) (alpha := (211753940771/898950000000000 : ℝ)) (beta := (3308103701/14046093750000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (17979/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(211753940771/898950000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3308103701/14046093750000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1466386369/5000000000 : ℝ)*X 0 0+(586428057/2000000000 : ℝ)*X 0 1+(-1584203713/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3633957513/10000000000 : ℝ)*X 1 0+(-3633173849/10000000000 : ℝ)*X 1 1+(-2556999373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5302073163/10000000000 : ℝ)*X 2 0+(132578003/250000000 : ℝ)*X 2 1+(1484259607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2519357839/5000000000 : ℝ)*X 0 0+(629963829/1250000000 : ℝ)*X 0 1+(-541421939/2500000000 : ℝ)*X 0 2+(2519357839/5000000000 : ℝ)*X 1 0+(629963829/1250000000 : ℝ)*X 1 1+(-541421939/2500000000 : ℝ)*X 1 2+(2519357839/5000000000 : ℝ)*X 2 0+(629963829/1250000000 : ℝ)*X 2 1+(-541421939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319048_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-140667641253603155389414084748529/17402044670000000000000000000000 : ℝ) := by norm_num
    linear_combination (199337/1000000000000 : ℝ)*(base5) + (5779/1000000000000 : ℝ)*(base7) + (149561/1000000000000 : ℝ)*(base12) + (32437/1000000000000 : ℝ)*(base15) + (183062479297/1000000000000 : ℝ)*(base39) + (7218383463/7812500000 : ℝ)*(base59) + (183737548659/500000000000 : ℝ)*(base60) + (4291/1000000000000 : ℝ)*(ratio_s0_0) + (92547/50000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (92547/50000 : ℝ)*(major_s1_2) + (538893124119/200000000000 : ℝ)*(sp_s1_0) + (2694465737719/1000000000000 : ℝ)*(sp_s1_1) + (2694465969493/1000000000000 : ℝ)*(sp_s1_2) + (499999903221/500000000000 : ℝ)*(sp_s1_6) + (673616442539/250000000000 : ℝ)*(f.sum) + (291211649393739/1260835000000000000000000000 : ℝ)*base63 + (1585646683659/4610000000000000000000000 : ℝ)*base64 + (208618099331/1367500000000000000000000 : ℝ)*base67 + (3243968628897/4610000000000000000000000 : ℝ)*base69 + (21461855555162593/31813610000000000000000000000 : ℝ)*base70 + (4320269226963/34505000000000000000000000 : ℝ)*base73 + (378215344571/1094000000000000000000000 : ℝ)*base75 + (1655734308513/8626250000000000000000000 : ℝ)*base76 + (1169661025424853/37748470000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p019_b027 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=48 := by omega
  rcases hc with rfl
  · exact collision_c319048 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
