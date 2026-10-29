-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:11:28.647999+00:00
-- url     : https://prove2.me/submissions/b1633eda-9eab-4dd3-81e8-ee3167a22c5f

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
theorem collision_support_c312068_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7606518069/10000000000 : ℝ)*x 0 + (1402963531/5000000000 : ℝ)*x 1 + (-205715031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7606518069/10000000000 : ℝ)^73 ≤ (4402654370899/6250000000000 : ℝ)^57 := by
    have hnat : (7606518069 : ℕ)^73*6250000000000^57 ≤ 4402654370899^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7606518069 10000000000 4402654370899 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402963531/5000000000 : ℝ)^73 ≤ (19640405433131/100000000000000 : ℝ)^57 := by
    have hnat : (1402963531 : ℕ)^73*100000000000000^57 ≤ 19640405433131^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402963531 5000000000 19640405433131 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205715031/1250000000 : ℝ)^73 ≤ (9917124613121/100000000000000 : ℝ)^57 := by
    have hnat : (205715031 : ℕ)^73*100000000000000^57 ≤ 9917124613121^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205715031 1250000000 9917124613121 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7606518069/10000000000 : ℝ), (1402963531/5000000000 : ℝ), (-205715031/1250000000 : ℝ)] ![(4402654370899/6250000000000 : ℝ), (19640405433131/100000000000000 : ℝ), (9917124613121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7606518069/10000000000 : ℝ)|^73 ≤ (4402654370899/6250000000000 : ℝ)^57
        have hw : |(7606518069/10000000000 : ℝ)|=(7606518069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402963531/5000000000 : ℝ)|^73 ≤ (19640405433131/100000000000000 : ℝ)^57
        have hw : |(1402963531/5000000000 : ℝ)|=(1402963531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205715031/1250000000 : ℝ)|^73 ≤ (9917124613121/100000000000000 : ℝ)^57
        have hw : |(-205715031/1250000000 : ℝ)|=(205715031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4169054629/10000000000 : ℝ)*x 0 + (-1084684999/2500000000 : ℝ)*x 1 + (4214255657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169054629/10000000000 : ℝ)^73 ≤ (32612303074941/100000000000000 : ℝ)^57 := by
    have hnat : (4169054629 : ℕ)^73*100000000000000^57 ≤ 32612303074941^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169054629 10000000000 32612303074941 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084684999/2500000000 : ℝ)^73 ≤ (8580467830309/25000000000000 : ℝ)^57 := by
    have hnat : (1084684999 : ℕ)^73*25000000000000^57 ≤ 8580467830309^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084684999 2500000000 8580467830309 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214255657/10000000000 : ℝ)^73 ≤ (8266456397289/25000000000000 : ℝ)^57 := by
    have hnat : (4214255657 : ℕ)^73*25000000000000^57 ≤ 8266456397289^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214255657 10000000000 8266456397289 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169054629/10000000000 : ℝ), (-1084684999/2500000000 : ℝ), (4214255657/10000000000 : ℝ)] ![(32612303074941/100000000000000 : ℝ), (8580467830309/25000000000000 : ℝ), (8266456397289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169054629/10000000000 : ℝ)|^73 ≤ (32612303074941/100000000000000 : ℝ)^57
        have hw : |(4169054629/10000000000 : ℝ)|=(4169054629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084684999/2500000000 : ℝ)|^73 ≤ (8580467830309/25000000000000 : ℝ)^57
        have hw : |(-1084684999/2500000000 : ℝ)|=(1084684999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214255657/10000000000 : ℝ)|^73 ≤ (8266456397289/25000000000000 : ℝ)^57
        have hw : |(4214255657/10000000000 : ℝ)|=(4214255657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-265296461/5000000000 : ℝ)*x 0 + (-5595310591/10000000000 : ℝ)*x 1 + (-583264519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265296461/5000000000 : ℝ)^73 ≤ (1163509032199/50000000000000 : ℝ)^57 := by
    have hnat : (265296461 : ℕ)^73*50000000000000^57 ≤ 1163509032199^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265296461 5000000000 1163509032199 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595310591/10000000000 : ℝ)^73 ≤ (47537682867349/100000000000000 : ℝ)^57 := by
    have hnat : (5595310591 : ℕ)^73*100000000000000^57 ≤ 47537682867349^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595310591 10000000000 47537682867349 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583264519/1000000000 : ℝ)^73 ≤ (10027059810343/20000000000000 : ℝ)^57 := by
    have hnat : (583264519 : ℕ)^73*20000000000000^57 ≤ 10027059810343^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583264519 1000000000 10027059810343 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265296461/5000000000 : ℝ), (-5595310591/10000000000 : ℝ), (-583264519/1000000000 : ℝ)] ![(1163509032199/50000000000000 : ℝ), (47537682867349/100000000000000 : ℝ), (10027059810343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265296461/5000000000 : ℝ)|^73 ≤ (1163509032199/50000000000000 : ℝ)^57
        have hw : |(-265296461/5000000000 : ℝ)|=(265296461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5595310591/10000000000 : ℝ)|^73 ≤ (47537682867349/100000000000000 : ℝ)^57
        have hw : |(-5595310591/10000000000 : ℝ)|=(5595310591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-583264519/1000000000 : ℝ)|^73 ≤ (10027059810343/20000000000000 : ℝ)^57
        have hw : |(-583264519/1000000000 : ℝ)|=(583264519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7634908933/10000000000 : ℝ)*x 0 + (67095471/200000000 : ℝ)*x 1 + (-446365459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7634908933/10000000000 : ℝ)^73 ≤ (70779371113293/100000000000000 : ℝ)^57 := by
    have hnat : (7634908933 : ℕ)^73*100000000000000^57 ≤ 70779371113293^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7634908933 10000000000 70779371113293 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67095471/200000000 : ℝ)^73 ≤ (12344856488697/50000000000000 : ℝ)^57 := by
    have hnat : (67095471 : ℕ)^73*50000000000000^57 ≤ 12344856488697^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67095471 200000000 12344856488697 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446365459/5000000000 : ℝ)^73 ≤ (566364487059/12500000000000 : ℝ)^57 := by
    have hnat : (446365459 : ℕ)^73*12500000000000^57 ≤ 566364487059^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446365459 5000000000 566364487059 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7634908933/10000000000 : ℝ), (67095471/200000000 : ℝ), (-446365459/5000000000 : ℝ)] ![(70779371113293/100000000000000 : ℝ), (12344856488697/50000000000000 : ℝ), (566364487059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7634908933/10000000000 : ℝ)|^73 ≤ (70779371113293/100000000000000 : ℝ)^57
        have hw : |(7634908933/10000000000 : ℝ)|=(7634908933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67095471/200000000 : ℝ)|^73 ≤ (12344856488697/50000000000000 : ℝ)^57
        have hw : |(67095471/200000000 : ℝ)|=(67095471/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446365459/5000000000 : ℝ)|^73 ≤ (566364487059/12500000000000 : ℝ)^57
        have hw : |(-446365459/5000000000 : ℝ)|=(446365459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4587057729/10000000000 : ℝ)*x 0 + (-3748037/12500000 : ℝ)*x 1 + (632108743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4587057729/10000000000 : ℝ)^73 ≤ (36857533048991/100000000000000 : ℝ)^57 := by
    have hnat : (4587057729 : ℕ)^73*100000000000000^57 ≤ 36857533048991^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587057729 10000000000 36857533048991 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3748037/12500000 : ℝ)^73 ≤ (21382429279107/100000000000000 : ℝ)^57 := by
    have hnat : (3748037 : ℕ)^73*100000000000000^57 ≤ 21382429279107^57*12500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3748037 12500000 21382429279107 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632108743/1250000000 : ℝ)^73 ≤ (41760037659441/100000000000000 : ℝ)^57 := by
    have hnat : (632108743 : ℕ)^73*100000000000000^57 ≤ 41760037659441^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632108743 1250000000 41760037659441 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4587057729/10000000000 : ℝ), (-3748037/12500000 : ℝ), (632108743/1250000000 : ℝ)] ![(36857533048991/100000000000000 : ℝ), (21382429279107/100000000000000 : ℝ), (41760037659441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4587057729/10000000000 : ℝ)|^73 ≤ (36857533048991/100000000000000 : ℝ)^57
        have hw : |(4587057729/10000000000 : ℝ)|=(4587057729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3748037/12500000 : ℝ)|^73 ≤ (21382429279107/100000000000000 : ℝ)^57
        have hw : |(-3748037/12500000 : ℝ)|=(3748037/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632108743/1250000000 : ℝ)|^73 ≤ (41760037659441/100000000000000 : ℝ)^57
        have hw : |(632108743/1250000000 : ℝ)|=(632108743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1000512023/2000000000 : ℝ)*x 0 + (-185358273/1250000000 : ℝ)*x 1 + (-583264519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000512023/2000000000 : ℝ)^73 ≤ (8237303492391/20000000000000 : ℝ)^57 := by
    have hnat : (1000512023 : ℕ)^73*20000000000000^57 ≤ 8237303492391^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000512023 2000000000 8237303492391 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185358273/1250000000 : ℝ)^73 ≤ (8678183475229/100000000000000 : ℝ)^57 := by
    have hnat : (185358273 : ℕ)^73*100000000000000^57 ≤ 8678183475229^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185358273 1250000000 8678183475229 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583264519/1000000000 : ℝ)^73 ≤ (10027059810343/20000000000000 : ℝ)^57 := by
    have hnat : (583264519 : ℕ)^73*20000000000000^57 ≤ 10027059810343^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583264519 1000000000 10027059810343 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1000512023/2000000000 : ℝ), (-185358273/1250000000 : ℝ), (-583264519/1000000000 : ℝ)] ![(8237303492391/20000000000000 : ℝ), (8678183475229/100000000000000 : ℝ), (10027059810343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1000512023/2000000000 : ℝ)|^73 ≤ (8237303492391/20000000000000 : ℝ)^57
        have hw : |(1000512023/2000000000 : ℝ)|=(1000512023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185358273/1250000000 : ℝ)|^73 ≤ (8678183475229/100000000000000 : ℝ)^57
        have hw : |(-185358273/1250000000 : ℝ)|=(185358273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-583264519/1000000000 : ℝ)|^73 ≤ (10027059810343/20000000000000 : ℝ)^57
        have hw : |(-583264519/1000000000 : ℝ)|=(583264519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-187678037/10000000000 : ℝ)*x 0 + (-2137817937/5000000000 : ℝ)*x 1 + (-9004669/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187678037/10000000000 : ℝ)^73 ≤ (307416790161/50000000000000 : ℝ)^57 := by
    have hnat : (187678037 : ℕ)^73*50000000000000^57 ≤ 307416790161^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187678037 10000000000 307416790161 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2137817937/5000000000 : ℝ)^73 ≤ (33683868626991/100000000000000 : ℝ)^57 := by
    have hnat : (2137817937 : ℕ)^73*100000000000000^57 ≤ 33683868626991^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137817937 5000000000 33683868626991 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9004669/12500000 : ℝ)^73 ≤ (65701297780671/100000000000000 : ℝ)^57 := by
    have hnat : (9004669 : ℕ)^73*100000000000000^57 ≤ 65701297780671^57*12500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9004669 12500000 65701297780671 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187678037/10000000000 : ℝ), (-2137817937/5000000000 : ℝ), (-9004669/12500000 : ℝ)] ![(307416790161/50000000000000 : ℝ), (33683868626991/100000000000000 : ℝ), (65701297780671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187678037/10000000000 : ℝ)|^73 ≤ (307416790161/50000000000000 : ℝ)^57
        have hw : |(-187678037/10000000000 : ℝ)|=(187678037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2137817937/5000000000 : ℝ)|^73 ≤ (33683868626991/100000000000000 : ℝ)^57
        have hw : |(-2137817937/5000000000 : ℝ)|=(2137817937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9004669/12500000 : ℝ)|^73 ≤ (65701297780671/100000000000000 : ℝ)^57
        have hw : |(-9004669/12500000 : ℝ)|=(9004669/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8954593917/10000000000 : ℝ)*x 0 + (179440741/1000000000 : ℝ)*x 1 + (-491192877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8954593917/10000000000 : ℝ)^73 ≤ (86813065996163/100000000000000 : ℝ)^57 := by
    have hnat : (8954593917 : ℕ)^73*100000000000000^57 ≤ 86813065996163^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8954593917 10000000000 86813065996163 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179440741/1000000000 : ℝ)^73 ≤ (276971698071/2500000000000 : ℝ)^57 := by
    have hnat : (179440741 : ℕ)^73*2500000000000^57 ≤ 276971698071^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179440741 1000000000 276971698071 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491192877/10000000000 : ℝ)^73 ≤ (2108066066877/100000000000000 : ℝ)^57 := by
    have hnat : (491192877 : ℕ)^73*100000000000000^57 ≤ 2108066066877^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491192877 10000000000 2108066066877 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8954593917/10000000000 : ℝ), (179440741/1000000000 : ℝ), (-491192877/10000000000 : ℝ)] ![(86813065996163/100000000000000 : ℝ), (276971698071/2500000000000 : ℝ), (2108066066877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8954593917/10000000000 : ℝ)|^73 ≤ (86813065996163/100000000000000 : ℝ)^57
        have hw : |(8954593917/10000000000 : ℝ)|=(8954593917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179440741/1000000000 : ℝ)|^73 ≤ (276971698071/2500000000000 : ℝ)^57
        have hw : |(179440741/1000000000 : ℝ)|=(179440741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491192877/10000000000 : ℝ)|^73 ≤ (2108066066877/100000000000000 : ℝ)^57
        have hw : |(-491192877/10000000000 : ℝ)|=(491192877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1174225269/2500000000 : ℝ)*x 0 + (-449692111/1000000000 : ℝ)*x 1 + (875236591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174225269/2500000000 : ℝ)^73 ≤ (37991662745357/100000000000000 : ℝ)^57 := by
    have hnat : (1174225269 : ℕ)^73*100000000000000^57 ≤ 37991662745357^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174225269 2500000000 37991662745357 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449692111/1000000000 : ℝ)^73 ≤ (898313620117/2500000000000 : ℝ)^57 := by
    have hnat : (449692111 : ℕ)^73*2500000000000^57 ≤ 898313620117^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449692111 1000000000 898313620117 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875236591/2500000000 : ℝ)^73 ≤ (26075792437447/100000000000000 : ℝ)^57 := by
    have hnat : (875236591 : ℕ)^73*100000000000000^57 ≤ 26075792437447^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875236591 2500000000 26075792437447 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1174225269/2500000000 : ℝ), (-449692111/1000000000 : ℝ), (875236591/2500000000 : ℝ)] ![(37991662745357/100000000000000 : ℝ), (898313620117/2500000000000 : ℝ), (26075792437447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1174225269/2500000000 : ℝ)|^73 ≤ (37991662745357/100000000000000 : ℝ)^57
        have hw : |(1174225269/2500000000 : ℝ)|=(1174225269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449692111/1000000000 : ℝ)|^73 ≤ (898313620117/2500000000000 : ℝ)^57
        have hw : |(-449692111/1000000000 : ℝ)|=(449692111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875236591/2500000000 : ℝ)|^73 ≤ (26075792437447/100000000000000 : ℝ)^57
        have hw : |(875236591/2500000000 : ℝ)|=(875236591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (63756041/250000000 : ℝ)*x 0 + (-156101063/625000000 : ℝ)*x 1 + (-9004669/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63756041/250000000 : ℝ)^73 ≤ (17378315261713/100000000000000 : ℝ)^57 := by
    have hnat : (63756041 : ℕ)^73*100000000000000^57 ≤ 17378315261713^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63756041 250000000 17378315261713 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156101063/625000000 : ℝ)^73 ≤ (1692038693829/10000000000000 : ℝ)^57 := by
    have hnat : (156101063 : ℕ)^73*10000000000000^57 ≤ 1692038693829^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156101063 625000000 1692038693829 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9004669/12500000 : ℝ)^73 ≤ (65701297780671/100000000000000 : ℝ)^57 := by
    have hnat : (9004669 : ℕ)^73*100000000000000^57 ≤ 65701297780671^57*12500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9004669 12500000 65701297780671 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63756041/250000000 : ℝ), (-156101063/625000000 : ℝ), (-9004669/12500000 : ℝ)] ![(17378315261713/100000000000000 : ℝ), (1692038693829/10000000000000 : ℝ), (65701297780671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63756041/250000000 : ℝ)|^73 ≤ (17378315261713/100000000000000 : ℝ)^57
        have hw : |(63756041/250000000 : ℝ)|=(63756041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156101063/625000000 : ℝ)|^73 ≤ (1692038693829/10000000000000 : ℝ)^57
        have hw : |(-156101063/625000000 : ℝ)|=(156101063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9004669/12500000 : ℝ)|^73 ≤ (65701297780671/100000000000000 : ℝ)^57
        have hw : |(-9004669/12500000 : ℝ)|=(9004669/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-165737707/10000000000 : ℝ)*x 0 + (-6378105957/10000000000 : ℝ)*x 1 + (-1299502771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165737707/10000000000 : ℝ)^73 ≤ (26216805541/5000000000000 : ℝ)^57 := by
    have hnat : (165737707 : ℕ)^73*5000000000000^57 ≤ 26216805541^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165737707 10000000000 26216805541 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6378105957/10000000000 : ℝ)^73 ≤ (56217089278103/100000000000000 : ℝ)^57 := by
    have hnat : (6378105957 : ℕ)^73*100000000000000^57 ≤ 56217089278103^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6378105957 10000000000 56217089278103 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299502771/2500000000 : ℝ)^73 ≤ (2703660912851/6250000000000 : ℝ)^57 := by
    have hnat : (1299502771 : ℕ)^73*6250000000000^57 ≤ 2703660912851^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299502771 2500000000 2703660912851 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-165737707/10000000000 : ℝ), (-6378105957/10000000000 : ℝ), (-1299502771/2500000000 : ℝ)] ![(26216805541/5000000000000 : ℝ), (56217089278103/100000000000000 : ℝ), (2703660912851/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-165737707/10000000000 : ℝ)|^73 ≤ (26216805541/5000000000000 : ℝ)^57
        have hw : |(-165737707/10000000000 : ℝ)|=(165737707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6378105957/10000000000 : ℝ)|^73 ≤ (56217089278103/100000000000000 : ℝ)^57
        have hw : |(-6378105957/10000000000 : ℝ)|=(6378105957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1299502771/2500000000 : ℝ)|^73 ≤ (2703660912851/6250000000000 : ℝ)^57
        have hw : |(-1299502771/2500000000 : ℝ)|=(1299502771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9015055027/10000000000 : ℝ)*x 0 + (1709527749/10000000000 : ℝ)*x 1 + (-475704249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9015055027/10000000000 : ℝ)^73 ≤ (1751289417737/2000000000000 : ℝ)^57 := by
    have hnat : (9015055027 : ℕ)^73*2000000000000^57 ≤ 1751289417737^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9015055027 10000000000 1751289417737 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1709527749/10000000000 : ℝ)^73 ≤ (10412215436849/100000000000000 : ℝ)^57 := by
    have hnat : (1709527749 : ℕ)^73*100000000000000^57 ≤ 10412215436849^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709527749 10000000000 10412215436849 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475704249/10000000000 : ℝ)^73 ≤ (1011656832311/50000000000000 : ℝ)^57 := by
    have hnat : (475704249 : ℕ)^73*50000000000000^57 ≤ 1011656832311^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475704249 10000000000 1011656832311 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9015055027/10000000000 : ℝ), (1709527749/10000000000 : ℝ), (-475704249/10000000000 : ℝ)] ![(1751289417737/2000000000000 : ℝ), (10412215436849/100000000000000 : ℝ), (1011656832311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9015055027/10000000000 : ℝ)|^73 ≤ (1751289417737/2000000000000 : ℝ)^57
        have hw : |(9015055027/10000000000 : ℝ)|=(9015055027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1709527749/10000000000 : ℝ)|^73 ≤ (10412215436849/100000000000000 : ℝ)^57
        have hw : |(1709527749/10000000000 : ℝ)|=(1709527749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475704249/10000000000 : ℝ)|^73 ≤ (1011656832311/50000000000000 : ℝ)^57
        have hw : |(-475704249/10000000000 : ℝ)|=(475704249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3482383107/10000000000 : ℝ)*x 0 + (-4643675229/10000000000 : ℝ)*x 1 + (913569849/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3482383107/10000000000 : ℝ)^73 ≤ (1657526439/6400000000 : ℝ)^57 := by
    have hnat : (3482383107 : ℕ)^73*6400000000^57 ≤ 1657526439^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3482383107 10000000000 1657526439 6400000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4643675229/10000000000 : ℝ)^73 ≤ (37441166576151/100000000000000 : ℝ)^57 := by
    have hnat : (4643675229 : ℕ)^73*100000000000000^57 ≤ 37441166576151^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643675229 10000000000 37441166576151 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (913569849/2000000000 : ℝ)^73 ≤ (1466399312119/4000000000000 : ℝ)^57 := by
    have hnat : (913569849 : ℕ)^73*4000000000000^57 ≤ 1466399312119^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913569849 2000000000 1466399312119 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3482383107/10000000000 : ℝ), (-4643675229/10000000000 : ℝ), (913569849/2000000000 : ℝ)] ![(1657526439/6400000000 : ℝ), (37441166576151/100000000000000 : ℝ), (1466399312119/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3482383107/10000000000 : ℝ)|^73 ≤ (1657526439/6400000000 : ℝ)^57
        have hw : |(3482383107/10000000000 : ℝ)|=(3482383107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4643675229/10000000000 : ℝ)|^73 ≤ (37441166576151/100000000000000 : ℝ)^57
        have hw : |(-4643675229/10000000000 : ℝ)|=(4643675229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(913569849/2000000000 : ℝ)|^73 ≤ (1466399312119/4000000000000 : ℝ)^57
        have hw : |(913569849/2000000000 : ℝ)|=(913569849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s0_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4119911547/10000000000 : ℝ)*x 0 + (-3347442209/10000000000 : ℝ)*x 1 + (-1299502771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119911547/10000000000 : ℝ)^73 ≤ (16060396093533/50000000000000 : ℝ)^57 := by
    have hnat : (4119911547 : ℕ)^73*50000000000000^57 ≤ 16060396093533^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119911547 10000000000 16060396093533 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3347442209/10000000000 : ℝ)^73 ≤ (24620633195053/100000000000000 : ℝ)^57 := by
    have hnat : (3347442209 : ℕ)^73*100000000000000^57 ≤ 24620633195053^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347442209 10000000000 24620633195053 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299502771/2500000000 : ℝ)^73 ≤ (2703660912851/6250000000000 : ℝ)^57 := by
    have hnat : (1299502771 : ℕ)^73*6250000000000^57 ≤ 2703660912851^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299502771 2500000000 2703660912851 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119911547/10000000000 : ℝ), (-3347442209/10000000000 : ℝ), (-1299502771/2500000000 : ℝ)] ![(16060396093533/50000000000000 : ℝ), (24620633195053/100000000000000 : ℝ), (2703660912851/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119911547/10000000000 : ℝ)|^73 ≤ (16060396093533/50000000000000 : ℝ)^57
        have hw : |(4119911547/10000000000 : ℝ)|=(4119911547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3347442209/10000000000 : ℝ)|^73 ≤ (24620633195053/100000000000000 : ℝ)^57
        have hw : |(-3347442209/10000000000 : ℝ)|=(3347442209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1299502771/2500000000 : ℝ)|^73 ≤ (2703660912851/6250000000000 : ℝ)^57
        have hw : |(-1299502771/2500000000 : ℝ)|=(1299502771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-573716737/2500000000 : ℝ)*x 0 + (-4831991029/10000000000 : ℝ)*x 1 + (-5399864771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (573716737/2500000000 : ℝ)^73 ≤ (15181721591967/100000000000000 : ℝ)^57 := by
    have hnat : (573716737 : ℕ)^73*100000000000000^57 ≤ 15181721591967^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573716737 2500000000 15181721591967 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4831991029/10000000000 : ℝ)^73 ≤ (7879338574901/20000000000000 : ℝ)^57 := by
    have hnat : (4831991029 : ℕ)^73*20000000000000^57 ≤ 7879338574901^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831991029 10000000000 7879338574901 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399864771/10000000000 : ℝ)^73 ≤ (45421585515677/100000000000000 : ℝ)^57 := by
    have hnat : (5399864771 : ℕ)^73*100000000000000^57 ≤ 45421585515677^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399864771 10000000000 45421585515677 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-573716737/2500000000 : ℝ), (-4831991029/10000000000 : ℝ), (-5399864771/10000000000 : ℝ)] ![(15181721591967/100000000000000 : ℝ), (7879338574901/20000000000000 : ℝ), (45421585515677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-573716737/2500000000 : ℝ)|^73 ≤ (15181721591967/100000000000000 : ℝ)^57
        have hw : |(-573716737/2500000000 : ℝ)|=(573716737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4831991029/10000000000 : ℝ)|^73 ≤ (7879338574901/20000000000000 : ℝ)^57
        have hw : |(-4831991029/10000000000 : ℝ)|=(4831991029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5399864771/10000000000 : ℝ)|^73 ≤ (45421585515677/100000000000000 : ℝ)^57
        have hw : |(-5399864771/10000000000 : ℝ)|=(5399864771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1554702431/2500000000 : ℝ)*x 0 + (3315464659/10000000000 : ℝ)*x 1 + (-373057317/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1554702431/2500000000 : ℝ)^73 ≤ (54425263136681/100000000000000 : ℝ)^57 := by
    have hnat : (1554702431 : ℕ)^73*100000000000000^57 ≤ 54425263136681^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554702431 2500000000 54425263136681 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3315464659/10000000000 : ℝ)^73 ≤ (2431982108929/10000000000000 : ℝ)^57 := by
    have hnat : (3315464659 : ℕ)^73*10000000000000^57 ≤ 2431982108929^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3315464659 10000000000 2431982108929 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373057317/1250000000 : ℝ)^73 ≤ (21254915753881/100000000000000 : ℝ)^57 := by
    have hnat : (373057317 : ℕ)^73*100000000000000^57 ≤ 21254915753881^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373057317 1250000000 21254915753881 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1554702431/2500000000 : ℝ), (3315464659/10000000000 : ℝ), (-373057317/1250000000 : ℝ)] ![(54425263136681/100000000000000 : ℝ), (2431982108929/10000000000000 : ℝ), (21254915753881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1554702431/2500000000 : ℝ)|^73 ≤ (54425263136681/100000000000000 : ℝ)^57
        have hw : |(1554702431/2500000000 : ℝ)|=(1554702431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3315464659/10000000000 : ℝ)|^73 ≤ (2431982108929/10000000000000 : ℝ)^57
        have hw : |(3315464659/10000000000 : ℝ)|=(3315464659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373057317/1250000000 : ℝ)|^73 ≤ (21254915753881/100000000000000 : ℝ)^57
        have hw : |(-373057317/1250000000 : ℝ)|=(373057317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4205466059/10000000000 : ℝ)*x 0 + (-4480527661/10000000000 : ℝ)*x 1 + (4033205117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205466059/10000000000 : ℝ)^73 ≤ (824438202789/2500000000000 : ℝ)^57 := by
    have hnat : (4205466059 : ℕ)^73*2500000000000^57 ≤ 824438202789^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205466059 10000000000 824438202789 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480527661/10000000000 : ℝ)^73 ≤ (8941217424767/25000000000000 : ℝ)^57 := by
    have hnat : (4480527661 : ℕ)^73*25000000000000^57 ≤ 8941217424767^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480527661 10000000000 8941217424767 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033205117/10000000000 : ℝ)^73 ≤ (31257602180587/100000000000000 : ℝ)^57 := by
    have hnat : (4033205117 : ℕ)^73*100000000000000^57 ≤ 31257602180587^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033205117 10000000000 31257602180587 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205466059/10000000000 : ℝ), (-4480527661/10000000000 : ℝ), (4033205117/10000000000 : ℝ)] ![(824438202789/2500000000000 : ℝ), (8941217424767/25000000000000 : ℝ), (31257602180587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205466059/10000000000 : ℝ)|^73 ≤ (824438202789/2500000000000 : ℝ)^57
        have hw : |(4205466059/10000000000 : ℝ)|=(4205466059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4480527661/10000000000 : ℝ)|^73 ≤ (8941217424767/25000000000000 : ℝ)^57
        have hw : |(-4480527661/10000000000 : ℝ)|=(4480527661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033205117/10000000000 : ℝ)|^73 ≤ (31257602180587/100000000000000 : ℝ)^57
        have hw : |(4033205117/10000000000 : ℝ)|=(4033205117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312068_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (983730177/2500000000 : ℝ)*x 0 + (-4145975171/10000000000 : ℝ)*x 1 + (-579153219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983730177/2500000000 : ℝ)^73 ≤ (30285434293871/100000000000000 : ℝ)^57 := by
    have hnat : (983730177 : ℕ)^73*100000000000000^57 ≤ 30285434293871^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983730177 2500000000 30285434293871 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145975171/10000000000 : ℝ)^73 ≤ (3238126716881/10000000000000 : ℝ)^57 := by
    have hnat : (4145975171 : ℕ)^73*10000000000000^57 ≤ 3238126716881^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145975171 10000000000 3238126716881 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579153219/1250000000 : ℝ)^73 ≤ (18666649262159/50000000000000 : ℝ)^57 := by
    have hnat : (579153219 : ℕ)^73*50000000000000^57 ≤ 18666649262159^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579153219 1250000000 18666649262159 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(983730177/2500000000 : ℝ), (-4145975171/10000000000 : ℝ), (-579153219/1250000000 : ℝ)] ![(30285434293871/100000000000000 : ℝ), (3238126716881/10000000000000 : ℝ), (18666649262159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(983730177/2500000000 : ℝ)|^73 ≤ (30285434293871/100000000000000 : ℝ)^57
        have hw : |(983730177/2500000000 : ℝ)|=(983730177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4145975171/10000000000 : ℝ)|^73 ≤ (3238126716881/10000000000000 : ℝ)^57
        have hw : |(-4145975171/10000000000 : ℝ)|=(4145975171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579153219/1250000000 : ℝ)|^73 ≤ (18666649262159/50000000000000 : ℝ)^57
        have hw : |(-579153219/1250000000 : ℝ)|=(579153219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312068 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((7606518069/10000000000 : ℝ)*X 1 0+(1402963531/5000000000 : ℝ)*X 1 1+(-205715031/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4169054629/10000000000 : ℝ)*X 2 0+(-1084684999/2500000000 : ℝ)*X 2 1+(4214255657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-265296461/5000000000 : ℝ)*X 0 0+(-5595310591/10000000000 : ℝ)*X 0 1+(-583264519/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7634908933/10000000000 : ℝ)*X 1 0+(67095471/200000000 : ℝ)*X 1 1+(-446365459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4587057729/10000000000 : ℝ)*X 2 0+(-3748037/12500000 : ℝ)*X 2 1+(632108743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1000512023/2000000000 : ℝ)*X 0 0+(-185358273/1250000000 : ℝ)*X 0 1+(-583264519/1000000000 : ℝ)*X 0 2+(1000512023/2000000000 : ℝ)*X 1 0+(-185358273/1250000000 : ℝ)*X 1 1+(-583264519/1000000000 : ℝ)*X 1 2+(1000512023/2000000000 : ℝ)*X 2 0+(-185358273/1250000000 : ℝ)*X 2 1+(-583264519/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-187678037/10000000000 : ℝ)*X 0 0+(-2137817937/5000000000 : ℝ)*X 0 1+(-9004669/12500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8954593917/10000000000 : ℝ)*X 1 0+(179440741/1000000000 : ℝ)*X 1 1+(-491192877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1174225269/2500000000 : ℝ)*X 2 0+(-449692111/1000000000 : ℝ)*X 2 1+(875236591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((63756041/250000000 : ℝ)*X 0 0+(-156101063/625000000 : ℝ)*X 0 1+(-9004669/12500000 : ℝ)*X 0 2+(63756041/250000000 : ℝ)*X 1 0+(-156101063/625000000 : ℝ)*X 1 1+(-9004669/12500000 : ℝ)*X 1 2+(63756041/250000000 : ℝ)*X 2 0+(-156101063/625000000 : ℝ)*X 2 1+(-9004669/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-165737707/10000000000 : ℝ)*X 0 0+(-6378105957/10000000000 : ℝ)*X 0 1+(-1299502771/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9015055027/10000000000 : ℝ)*X 1 0+(1709527749/10000000000 : ℝ)*X 1 1+(-475704249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3482383107/10000000000 : ℝ)*X 2 0+(-4643675229/10000000000 : ℝ)*X 2 1+(913569849/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4119911547/10000000000 : ℝ)*X 0 0+(-3347442209/10000000000 : ℝ)*X 0 1+(-1299502771/2500000000 : ℝ)*X 0 2+(4119911547/10000000000 : ℝ)*X 1 0+(-3347442209/10000000000 : ℝ)*X 1 1+(-1299502771/2500000000 : ℝ)*X 1 2+(4119911547/10000000000 : ℝ)*X 2 0+(-3347442209/10000000000 : ℝ)*X 2 1+(-1299502771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((20951/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20951/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (886099687133632849569/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (351732357183/250000000000 : ℝ)*(base1) + (458416380497/250000000000 : ℝ)*(base39) + (91705375239/250000000000 : ℝ)*(base49) + (487623910619/200000000000 : ℝ)*(major_s0_0) + (487623910619/200000000000 : ℝ)*(major_s0_1) + (487623910619/200000000000 : ℝ)*(major_s0_2) + (12663219/250000000000 : ℝ)*(sp_s0_1) + (4822440189897/1000000000000 : ℝ)*(sp_s0_7) + (3415465322879/1000000000000 : ℝ)*(sp_s0_8) + (1707743871007/500000000000 : ℝ)*(sp_s0_9) + (6722921201/125000000000 : ℝ)*(sp_s0_13) + (12593011/1000000000000 : ℝ)*(sp_s0_14) + (368921/50000000000 : ℝ)*(sp_s0_15) + (17806081/500000000000 : ℝ)*(sp_s0_23) + (1460712798341/1000000000000 : ℝ)*(f.failure) + (53367552409/15625000000 : ℝ)*(f.sum) + (11178907393477/400000000000000000000000000 : ℝ)*base63 + (1341933899854369/2000000000000000000000000000 : ℝ)*base64 + (847801212610877/1000000000000000000000000000 : ℝ)*base66 + (1332947966510877/1000000000000000000000000000 : ℝ)*base69 + (73352482953477/400000000000000000000000000 : ℝ)*base71 + (1531122571545631/2000000000000000000000000000 : ℝ)*base72 + (594392085545631/2000000000000000000000000000 : ℝ)*base75 + (364198435389123/1000000000000000000000000000 : ℝ)*base76 + (181148341993477/400000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (8667/100000000000000000 : ℝ)*base86 + (8667/100000000000000000 : ℝ)*base88 + (8667/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-54919/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-54919/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2545313784631687777941/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1412316006463/1000000000000 : ℝ)*(base1) + (4094117/1000000000000 : ℝ)*(base21) + (2438216009789/1000000000000 : ℝ)*(base39) + (649142143283/1000000000000 : ℝ)*(base49) + (517576473373/1000000000000 : ℝ)*(base60) + (1823369036391/500000000000 : ℝ)*(major_s0_0) + (1823369036391/500000000000 : ℝ)*(major_s0_1) + (1823369036391/500000000000 : ℝ)*(major_s0_2) + (35447/3125000000 : ℝ)*(sp_s0_8) + (8846977/500000000000 : ℝ)*(sp_s0_9) + (652097676611/100000000000 : ℝ)*(sp_s0_14) + (2554324708303/500000000000 : ℝ)*(sp_s0_15) + (638579871447/125000000000 : ℝ)*(sp_s0_16) + (386248841287/500000000000 : ℝ)*(sp_s0_20) + (2184813689037/1000000000000 : ℝ)*(f.failure) + (5108660759647/1000000000000 : ℝ)*(f.sum) + (70358090792647/1000000000000000000000000000 : ℝ)*base62 + (2131581158444859/5000000000000000000000000000 : ℝ)*base65 + (1268979000704047/2500000000000000000000000000 : ℝ)*base67 + (905404353795953/2500000000000000000000000000 : ℝ)*base69 + (373625051407353/1000000000000000000000000000 : ℝ)*base71 + (48441301444859/5000000000000000000000000000 : ℝ)*base72 + (3292577008555141/5000000000000000000000000000 : ℝ)*base74 + (518796787295953/2500000000000000000000000000 : ℝ)*base77 + (199993782207353/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (32781/100000000000000000 : ℝ)*base87 + (32781/100000000000000000 : ℝ)*base89 + (32781/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9869/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9869/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8327803121926171791159/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163535835787/1000000000000 : ℝ)*(base1) + (1282465207279/1000000000000 : ℝ)*(base39) + (550487035433/1000000000000 : ℝ)*(base49) + (7102319/500000000000 : ℝ)*(base60) + (3110115777709/1000000000000 : ℝ)*(major_s0_0) + (3110115777709/1000000000000 : ℝ)*(major_s0_1) + (3110115777709/1000000000000 : ℝ)*(major_s0_2) + (158225083/1000000000000 : ℝ)*(sp_s0_2) + (19146571/1000000000000 : ℝ)*(sp_s0_9) + (304513461/100000000000 : ℝ)*(sp_s0_15) + (1130111588249/250000000000 : ℝ)*(sp_s0_21) + (4353865382599/1000000000000 : ℝ)*(sp_s0_22) + (871346629111/200000000000 : ℝ)*(sp_s0_23) + (33995593011/20000000000 : ℝ)*(sp_s0_27) + (1863315486337/1000000000000 : ℝ)*(f.failure) + (4356910517209/1000000000000 : ℝ)*(f.sum) + (545894416952947/2000000000000000000000000000 : ℝ)*base63 + (6215023774116041/10000000000000000000000000000 : ℝ)*base65 + (1532056376675653/5000000000000000000000000000 : ℝ)*base67 + (975923858824347/5000000000000000000000000000 : ℝ)*base69 + (1089223592352947/2000000000000000000000000000 : ℝ)*base71 + (322729331116041/10000000000000000000000000000 : ℝ)*base72 + (2305935048883959/10000000000000000000000000000 : ℝ)*base74 + (1309817211824347/5000000000000000000000000000 : ℝ)*base77 + (219503818552947/2000000000000000000000000000 : ℝ)*base78 + (67681/100000000000000000 : ℝ)*base87 + (67681/100000000000000000 : ℝ)*base89 + (67681/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (20951/100000 : ℝ) ^ (9/2 : ℝ) ≤ (44095209486589991/50000000000000000000 : ℝ) := by
    have hpowers : (20951/100000 : ℝ)^9 ≤ (44095209486589991/50000000000000000000 : ℝ)^2 := by
      have hnat : (20951 : ℕ)^9*50000000000000000000^2 ≤ 44095209486589991^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20951 100000 44095209486589991 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20951/100000 : ℝ)) (X := (44095209486589991/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50044095209486589991/50000000000000000000 : ℝ) ≤ (625122444706587/625000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50044095209486589991/50000000000000000000 : ℝ)^2 ≤ (625122444706587/625000000000000 : ℝ)^9 := by
      have hnat : (50044095209486589991 : ℕ)^2*625000000000000^9 ≤ 625122444706587^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044095209486589991 50000000000000000000 625122444706587 625000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625122444706587/625000000000000 : ℝ)) (X := (50044095209486589991/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25044095209486589991/25000000000000000000 : ℝ) ≤ (5001958444223729/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25044095209486589991/25000000000000000000 : ℝ)^2 ≤ (5001958444223729/5000000000000000 : ℝ)^9 := by
      have hnat : (25044095209486589991 : ℕ)^2*5000000000000000^9 ≤ 5001958444223729^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044095209486589991 25000000000000000000 5001958444223729 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001958444223729/5000000000000000 : ℝ)) (X := (25044095209486589991/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(17492100941/18706250000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(139840938719/149650000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (20951/100000 : ℝ)) (alpha := (17492100941/18706250000000 : ℝ)) (beta := (139840938719/149650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20951/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(17492100941/18706250000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(139840938719/149650000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (54919/100000 : ℝ) ^ (9/2 : ℝ) ≤ (3370713167642632931/50000000000000000000 : ℝ) := by
    have hpowers : (54919/100000 : ℝ)^9 ≤ (3370713167642632931/50000000000000000000 : ℝ)^2 := by
      have hnat : (54919 : ℕ)^9*50000000000000000000^2 ≤ 3370713167642632931^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54919 100000 3370713167642632931 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54919/100000 : ℝ)) (X := (3370713167642632931/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (53370713167642632931/50000000000000000000 : ℝ) ≤ (10146031880716207/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (53370713167642632931/50000000000000000000 : ℝ)^2 ≤ (10146031880716207/10000000000000000 : ℝ)^9 := by
      have hnat : (53370713167642632931 : ℕ)^2*10000000000000000^9 ≤ 10146031880716207^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53370713167642632931 50000000000000000000 10146031880716207 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10146031880716207/10000000000000000 : ℝ)) (X := (53370713167642632931/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (28370713167642632931/25000000000000000000 : ℝ) ≤ (5142528713775961/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (28370713167642632931/25000000000000000000 : ℝ)^2 ≤ (5142528713775961/5000000000000000 : ℝ)^9 := by
      have hnat : (28370713167642632931 : ℕ)^2*5000000000000000^9 ≤ 5142528713775961^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28370713167642632931 25000000000000000000 5142528713775961 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5142528713775961/5000000000000000 : ℝ)) (X := (28370713167642632931/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(146031880716207/5491900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(27805109367143/1098380000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (54919/100000 : ℝ)) (alpha := (146031880716207/5491900000000000 : ℝ)) (beta := (27805109367143/1098380000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (54919/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(146031880716207/5491900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(27805109367143/1098380000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9869/25000 : ℝ) ^ (9/2 : ℝ) ≤ (61032213719888881/4000000000000000000 : ℝ) := by
    have hpowers : (9869/25000 : ℝ)^9 ≤ (61032213719888881/4000000000000000000 : ℝ)^2 := by
      have hnat : (9869 : ℕ)^9*4000000000000000000^2 ≤ 61032213719888881^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9869 25000 61032213719888881 4000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9869/25000 : ℝ)) (X := (61032213719888881/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4061032213719888881/4000000000000000000 : ℝ) ≤ (10033707393219401/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (4061032213719888881/4000000000000000000 : ℝ)^2 ≤ (10033707393219401/10000000000000000 : ℝ)^9 := by
      have hnat : (4061032213719888881 : ℕ)^2*10000000000000000^9 ≤ 10033707393219401^9*4000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4061032213719888881 4000000000000000000 10033707393219401 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10033707393219401/10000000000000000 : ℝ)) (X := (4061032213719888881/4000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2061032213719888881/2000000000000000000 : ℝ) ≤ (2516755763351403/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2061032213719888881/2000000000000000000 : ℝ)^2 ≤ (2516755763351403/2500000000000000 : ℝ)^9 := by
      have hnat : (2061032213719888881 : ℕ)^2*2500000000000000^9 ≤ 2516755763351403^9*2000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2061032213719888881 2000000000000000000 2516755763351403 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2516755763351403/2500000000000000 : ℝ)) (X := (2061032213719888881/2000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(33707393219401/3947600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(33315660186211/3947600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (9869/25000 : ℝ)) (alpha := (33707393219401/3947600000000000 : ℝ)) (beta := (33315660186211/3947600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9869/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(33707393219401/3947600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(33315660186211/3947600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-573716737/2500000000 : ℝ)*X 0 0+(-4831991029/10000000000 : ℝ)*X 0 1+(-5399864771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1554702431/2500000000 : ℝ)*X 1 0+(3315464659/10000000000 : ℝ)*X 1 1+(-373057317/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4205466059/10000000000 : ℝ)*X 2 0+(-4480527661/10000000000 : ℝ)*X 2 1+(4033205117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((983730177/2500000000 : ℝ)*X 0 0+(-4145975171/10000000000 : ℝ)*X 0 1+(-579153219/1250000000 : ℝ)*X 0 2+(983730177/2500000000 : ℝ)*X 1 0+(-4145975171/10000000000 : ℝ)*X 1 1+(-579153219/1250000000 : ℝ)*X 1 2+(983730177/2500000000 : ℝ)*X 2 0+(-4145975171/10000000000 : ℝ)*X 2 1+(-579153219/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-11416785134390905500274729878951/1643725670000000000000000000000 : ℝ) := by norm_num
    linear_combination (1751/1000000000000 : ℝ)*(base22) + (728907000491/1000000000000 : ℝ)*(base39) + (107814325039/500000000000 : ℝ)*(base40) + (10388975907/40000000000 : ℝ)*(base49) + (149904336461/1000000000000 : ℝ)*(base60) + (166913/100000 : ℝ)*(major_s1_0) + (166913/100000 : ℝ)*(major_s1_1) + (166913/100000 : ℝ)*(major_s1_2) + (144701572789/62500000000 : ℝ)*(sp_s1_0) + (578806290981/250000000000 : ℝ)*(sp_s1_1) + (2315225161443/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2315225162571/1000000000000 : ℝ)*(f.sum) + (146127072369527767/338747256875000000000000000000 : ℝ)*base63 + (38940734357/3084062500000000000000000 : ℝ)*base65 + (70453075531985661/34324375000000000000000000 : ℝ)*base67 + (4171894489084567/3084062500000000000000000 : ℝ)*base68 + (7474985888829743/73844792500000000000000000000 : ℝ)*base70 + (368837737339/935312500000000000000000 : ℝ)*base72 + (368492121479097/549190000000000000000000000 : ℝ)*base75 + (20551212754761/29930000000000000000000000 : ℝ)*base76 + (1025377017912871204177/1643725670000000000000000000000 : ℝ)*base78 + (2053/1000000000000 : ℝ)*base81 + (1353/1000000000000 : ℝ)*base83 + (623/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p012_b027 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 := by omega
  rcases hc with rfl
  · exact collision_c312068 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p012_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
