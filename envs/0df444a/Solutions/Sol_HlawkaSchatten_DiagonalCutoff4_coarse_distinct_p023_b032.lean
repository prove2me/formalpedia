-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:51:11.26901+00:00
-- url     : https://prove2.me/submissions/7a023b41-f3cb-4d83-88c3-3d880d8acdb8

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
theorem collision_support_c323057_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2946068077/10000000000 : ℝ)*x 0 + (2946068489/10000000000 : ℝ)*x 1 + (6236139733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2946068077/10000000000 : ℝ)^21 ≤ (4419658584097/20000000000000 : ℝ)^17 := by
    have hnat : (2946068077 : ℕ)^21*20000000000000^17 ≤ 4419658584097^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946068077 10000000000 4419658584097 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2946068489/10000000000 : ℝ)^21 ≤ (2762287092253/12500000000000 : ℝ)^17 := by
    have hnat : (2946068489 : ℕ)^21*12500000000000^17 ≤ 2762287092253^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946068489 10000000000 2762287092253 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6236139733/10000000000 : ℝ)^21 ≤ (6975426290603/12500000000000 : ℝ)^17 := by
    have hnat : (6236139733 : ℕ)^21*12500000000000^17 ≤ 6975426290603^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6236139733 10000000000 6975426290603 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2946068077/10000000000 : ℝ), (2946068489/10000000000 : ℝ), (6236139733/10000000000 : ℝ)] ![(4419658584097/20000000000000 : ℝ), (2762287092253/12500000000000 : ℝ), (6975426290603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2946068077/10000000000 : ℝ)|^21 ≤ (4419658584097/20000000000000 : ℝ)^17
        have hw : |(-2946068077/10000000000 : ℝ)|=(2946068077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2946068489/10000000000 : ℝ)|^21 ≤ (2762287092253/12500000000000 : ℝ)^17
        have hw : |(2946068489/10000000000 : ℝ)|=(2946068489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6236139733/10000000000 : ℝ)|^21 ≤ (6975426290603/12500000000000 : ℝ)^17
        have hw : |(6236139733/10000000000 : ℝ)|=(6236139733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2946068077/10000000000 : ℝ)*x 0 + (-2946068489/10000000000 : ℝ)*x 1 + (6236139733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2946068077/10000000000 : ℝ)^21 ≤ (4419658584097/20000000000000 : ℝ)^17 := by
    have hnat : (2946068077 : ℕ)^21*20000000000000^17 ≤ 4419658584097^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946068077 10000000000 4419658584097 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2946068489/10000000000 : ℝ)^21 ≤ (2762287092253/12500000000000 : ℝ)^17 := by
    have hnat : (2946068489 : ℕ)^21*12500000000000^17 ≤ 2762287092253^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946068489 10000000000 2762287092253 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6236139733/10000000000 : ℝ)^21 ≤ (6975426290603/12500000000000 : ℝ)^17 := by
    have hnat : (6236139733 : ℕ)^21*12500000000000^17 ≤ 6975426290603^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6236139733 10000000000 6975426290603 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2946068077/10000000000 : ℝ), (-2946068489/10000000000 : ℝ), (6236139733/10000000000 : ℝ)] ![(4419658584097/20000000000000 : ℝ), (2762287092253/12500000000000 : ℝ), (6975426290603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2946068077/10000000000 : ℝ)|^21 ≤ (4419658584097/20000000000000 : ℝ)^17
        have hw : |(2946068077/10000000000 : ℝ)|=(2946068077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2946068489/10000000000 : ℝ)|^21 ≤ (2762287092253/12500000000000 : ℝ)^17
        have hw : |(-2946068489/10000000000 : ℝ)|=(2946068489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6236139733/10000000000 : ℝ)|^21 ≤ (6975426290603/12500000000000 : ℝ)^17
        have hw : |(6236139733/10000000000 : ℝ)|=(6236139733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (22822807/40000000 : ℝ)*x 0 + (1426425337/2500000000 : ℝ)*x 1 + (-61/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22822807/40000000 : ℝ)^21 ≤ (25000001082671/50000000000000 : ℝ)^17 := by
    have hnat : (22822807 : ℕ)^21*50000000000000^17 ≤ 25000001082671^17*40000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22822807 40000000 25000001082671 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426425337/2500000000 : ℝ)^21 ≤ (49999997813657/100000000000000 : ℝ)^17 := by
    have hnat : (1426425337 : ℕ)^21*100000000000000^17 ≤ 49999997813657^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426425337 2500000000 49999997813657 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61/10000000000 : ℝ)^21 ≤ (89/1250000000000 : ℝ)^17 := by
    have hnat : (61 : ℕ)^21*1250000000000^17 ≤ 89^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61 10000000000 89 1250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22822807/40000000 : ℝ), (1426425337/2500000000 : ℝ), (-61/10000000000 : ℝ)] ![(25000001082671/50000000000000 : ℝ), (49999997813657/100000000000000 : ℝ), (89/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22822807/40000000 : ℝ)|^21 ≤ (25000001082671/50000000000000 : ℝ)^17
        have hw : |(22822807/40000000 : ℝ)|=(22822807/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426425337/2500000000 : ℝ)|^21 ≤ (49999997813657/100000000000000 : ℝ)^17
        have hw : |(1426425337/2500000000 : ℝ)|=(1426425337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61/10000000000 : ℝ)|^21 ≤ (89/1250000000000 : ℝ)^17
        have hw : |(-61/10000000000 : ℝ)|=(61/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2309038823/10000000000 : ℝ)*x 0 + (32759733/500000000 : ℝ)*x 1 + (4181896121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2309038823/10000000000 : ℝ)^21 ≤ (16354992492243/100000000000000 : ℝ)^17 := by
    have hnat : (2309038823 : ℕ)^21*100000000000000^17 ≤ 16354992492243^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309038823 10000000000 16354992492243 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32759733/500000000 : ℝ)^21 ≤ (431299811017/12500000000000 : ℝ)^17 := by
    have hnat : (32759733 : ℕ)^21*12500000000000^17 ≤ 431299811017^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32759733 500000000 431299811017 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4181896121/5000000000 : ℝ)^21 ≤ (20048652251213/25000000000000 : ℝ)^17 := by
    have hnat : (4181896121 : ℕ)^21*25000000000000^17 ≤ 20048652251213^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181896121 5000000000 20048652251213 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2309038823/10000000000 : ℝ), (32759733/500000000 : ℝ), (4181896121/5000000000 : ℝ)] ![(16354992492243/100000000000000 : ℝ), (431299811017/12500000000000 : ℝ), (20048652251213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2309038823/10000000000 : ℝ)|^21 ≤ (16354992492243/100000000000000 : ℝ)^17
        have hw : |(-2309038823/10000000000 : ℝ)|=(2309038823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32759733/500000000 : ℝ)|^21 ≤ (431299811017/12500000000000 : ℝ)^17
        have hw : |(32759733/500000000 : ℝ)|=(32759733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4181896121/5000000000 : ℝ)|^21 ≤ (20048652251213/25000000000000 : ℝ)^17
        have hw : |(4181896121/5000000000 : ℝ)|=(4181896121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1598148727/10000000000 : ℝ)*x 0 + (-1477880257/10000000000 : ℝ)*x 1 + (8363791993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1598148727/10000000000 : ℝ)^21 ≤ (5190426047991/50000000000000 : ℝ)^17 := by
    have hnat : (1598148727 : ℕ)^21*50000000000000^17 ≤ 5190426047991^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598148727 10000000000 5190426047991 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477880257/10000000000 : ℝ)^21 ≤ (294516932511/3125000000000 : ℝ)^17 := by
    have hnat : (1477880257 : ℕ)^21*3125000000000^17 ≤ 294516932511^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477880257 10000000000 294516932511 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8363791993/10000000000 : ℝ)^21 ≤ (40097303027801/50000000000000 : ℝ)^17 := by
    have hnat : (8363791993 : ℕ)^21*50000000000000^17 ≤ 40097303027801^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8363791993 10000000000 40097303027801 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1598148727/10000000000 : ℝ), (-1477880257/10000000000 : ℝ), (8363791993/10000000000 : ℝ)] ![(5190426047991/50000000000000 : ℝ), (294516932511/3125000000000 : ℝ), (40097303027801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1598148727/10000000000 : ℝ)|^21 ≤ (5190426047991/50000000000000 : ℝ)^17
        have hw : |(1598148727/10000000000 : ℝ)|=(1598148727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1477880257/10000000000 : ℝ)|^21 ≤ (294516932511/3125000000000 : ℝ)^17
        have hw : |(-1477880257/10000000000 : ℝ)|=(1477880257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8363791993/10000000000 : ℝ)|^21 ≤ (40097303027801/50000000000000 : ℝ)^17
        have hw : |(8363791993/10000000000 : ℝ)|=(8363791993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (453457097/1250000000 : ℝ)*x 0 + (7615144531/10000000000 : ℝ)*x 1 + (-572801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453457097/1250000000 : ℝ)^21 ≤ (14288243002681/50000000000000 : ℝ)^17 := by
    have hnat : (453457097 : ℕ)^21*50000000000000^17 ≤ 14288243002681^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453457097 1250000000 14288243002681 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7615144531/10000000000 : ℝ)^21 ≤ (17855734671603/25000000000000 : ℝ)^17 := by
    have hnat : (7615144531 : ℕ)^21*25000000000000^17 ≤ 17855734671603^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7615144531 10000000000 17855734671603 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572801/10000000000 : ℝ)^21 ≤ (287645121/50000000000000 : ℝ)^17 := by
    have hnat : (572801 : ℕ)^21*50000000000000^17 ≤ 287645121^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572801 10000000000 287645121 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(453457097/1250000000 : ℝ), (7615144531/10000000000 : ℝ), (-572801/10000000000 : ℝ)] ![(14288243002681/50000000000000 : ℝ), (17855734671603/25000000000000 : ℝ), (287645121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(453457097/1250000000 : ℝ)|^21 ≤ (14288243002681/50000000000000 : ℝ)^17
        have hw : |(453457097/1250000000 : ℝ)|=(453457097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7615144531/10000000000 : ℝ)|^21 ≤ (17855734671603/25000000000000 : ℝ)^17
        have hw : |(7615144531/10000000000 : ℝ)|=(7615144531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-572801/10000000000 : ℝ)|^21 ≤ (287645121/50000000000000 : ℝ)^17
        have hw : |(-572801/10000000000 : ℝ)|=(572801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (592425913/2500000000 : ℝ)*x 0 + (7615144531/10000000000 : ℝ)*x 1 + (1759393403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592425913/2500000000 : ℝ)^21 ≤ (1055463552053/6250000000000 : ℝ)^17 := by
    have hnat : (592425913 : ℕ)^21*6250000000000^17 ≤ 1055463552053^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592425913 2500000000 1055463552053 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7615144531/10000000000 : ℝ)^21 ≤ (17855734671603/25000000000000 : ℝ)^17 := by
    have hnat : (7615144531 : ℕ)^21*25000000000000^17 ≤ 17855734671603^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7615144531 10000000000 17855734671603 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759393403/10000000000 : ℝ)^21 ≤ (11689644466479/100000000000000 : ℝ)^17 := by
    have hnat : (1759393403 : ℕ)^21*100000000000000^17 ≤ 11689644466479^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759393403 10000000000 11689644466479 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(592425913/2500000000 : ℝ), (7615144531/10000000000 : ℝ), (1759393403/10000000000 : ℝ)] ![(1055463552053/6250000000000 : ℝ), (17855734671603/25000000000000 : ℝ), (11689644466479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(592425913/2500000000 : ℝ)|^21 ≤ (1055463552053/6250000000000 : ℝ)^17
        have hw : |(592425913/2500000000 : ℝ)|=(592425913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7615144531/10000000000 : ℝ)|^21 ≤ (17855734671603/25000000000000 : ℝ)^17
        have hw : |(7615144531/10000000000 : ℝ)|=(7615144531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1759393403/10000000000 : ℝ)|^21 ≤ (11689644466479/100000000000000 : ℝ)^17
        have hw : |(1759393403/10000000000 : ℝ)|=(1759393403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-9976481/78125000 : ℝ)*x 0 + (432277073/2500000000 : ℝ)*x 1 + (8405605969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9976481/78125000 : ℝ)^21 ≤ (786825616091/10000000000000 : ℝ)^17 := by
    have hnat : (9976481 : ℕ)^21*10000000000000^17 ≤ 786825616091^17*78125000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9976481 78125000 786825616091 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432277073/2500000000 : ℝ)^21 ≤ (1430198281961/12500000000000 : ℝ)^17 := by
    have hnat : (432277073 : ℕ)^21*12500000000000^17 ≤ 1430198281961^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432277073 2500000000 1430198281961 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8405605969/10000000000 : ℝ)^21 ≤ (8069015757391/10000000000000 : ℝ)^17 := by
    have hnat : (8405605969 : ℕ)^21*10000000000000^17 ≤ 8069015757391^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8405605969 10000000000 8069015757391 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9976481/78125000 : ℝ), (432277073/2500000000 : ℝ), (8405605969/10000000000 : ℝ)] ![(786825616091/10000000000000 : ℝ), (1430198281961/12500000000000 : ℝ), (8069015757391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9976481/78125000 : ℝ)|^21 ≤ (786825616091/10000000000000 : ℝ)^17
        have hw : |(-9976481/78125000 : ℝ)|=(9976481/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432277073/2500000000 : ℝ)|^21 ≤ (1430198281961/12500000000000 : ℝ)^17
        have hw : |(432277073/2500000000 : ℝ)|=(432277073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8405605969/10000000000 : ℝ)|^21 ≤ (8069015757391/10000000000000 : ℝ)^17
        have hw : |(8405605969/10000000000 : ℝ)|=(8405605969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (193972613/2500000000 : ℝ)*x 0 + (-539912237/2500000000 : ℝ)*x 1 + (1681121141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193972613/2500000000 : ℝ)^21 ≤ (2125920297073/50000000000000 : ℝ)^17 := by
    have hnat : (193972613 : ℕ)^21*50000000000000^17 ≤ 2125920297073^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193972613 2500000000 2125920297073 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539912237/2500000000 : ℝ)^21 ≤ (15058004949063/100000000000000 : ℝ)^17 := by
    have hnat : (539912237 : ℕ)^21*100000000000000^17 ≤ 15058004949063^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539912237 2500000000 15058004949063 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1681121141/2000000000 : ℝ)^21 ≤ (40345077221661/50000000000000 : ℝ)^17 := by
    have hnat : (1681121141 : ℕ)^21*50000000000000^17 ≤ 40345077221661^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681121141 2000000000 40345077221661 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(193972613/2500000000 : ℝ), (-539912237/2500000000 : ℝ), (1681121141/2000000000 : ℝ)] ![(2125920297073/50000000000000 : ℝ), (15058004949063/100000000000000 : ℝ), (40345077221661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(193972613/2500000000 : ℝ)|^21 ≤ (2125920297073/50000000000000 : ℝ)^17
        have hw : |(193972613/2500000000 : ℝ)|=(193972613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539912237/2500000000 : ℝ)|^21 ≤ (15058004949063/100000000000000 : ℝ)^17
        have hw : |(-539912237/2500000000 : ℝ)|=(539912237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1681121141/2000000000 : ℝ)|^21 ≤ (40345077221661/50000000000000 : ℝ)^17
        have hw : |(1681121141/2000000000 : ℝ)|=(1681121141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7972080431/10000000000 : ℝ)*x 0 + (3194069961/10000000000 : ℝ)*x 1 + (-282313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7972080431/10000000000 : ℝ)^21 ≤ (15116180206453/20000000000000 : ℝ)^17 := by
    have hnat : (7972080431 : ℕ)^21*20000000000000^17 ≤ 15116180206453^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7972080431 10000000000 15116180206453 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3194069961/10000000000 : ℝ)^21 ≤ (24418533785999/100000000000000 : ℝ)^17 := by
    have hnat : (3194069961 : ℕ)^21*100000000000000^17 ≤ 24418533785999^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194069961 10000000000 24418533785999 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282313/5000000000 : ℝ)^21 ≤ (565164919/100000000000000 : ℝ)^17 := by
    have hnat : (282313 : ℕ)^21*100000000000000^17 ≤ 565164919^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282313 5000000000 565164919 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7972080431/10000000000 : ℝ), (3194069961/10000000000 : ℝ), (-282313/5000000000 : ℝ)] ![(15116180206453/20000000000000 : ℝ), (24418533785999/100000000000000 : ℝ), (565164919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7972080431/10000000000 : ℝ)|^21 ≤ (15116180206453/20000000000000 : ℝ)^17
        have hw : |(7972080431/10000000000 : ℝ)|=(7972080431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3194069961/10000000000 : ℝ)|^21 ≤ (24418533785999/100000000000000 : ℝ)^17
        have hw : |(3194069961/10000000000 : ℝ)|=(3194069961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282313/5000000000 : ℝ)|^21 ≤ (565164919/100000000000000 : ℝ)^17
        have hw : |(-282313/5000000000 : ℝ)|=(282313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (724210729/1000000000 : ℝ)*x 0 + (708632423/2500000000 : ℝ)*x 1 + (1773358381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (724210729/1000000000 : ℝ)^21 ≤ (16781547683329/25000000000000 : ℝ)^17 := by
    have hnat : (724210729 : ℕ)^21*25000000000000^17 ≤ 16781547683329^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724210729 1000000000 16781547683329 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708632423/2500000000 : ℝ)^21 ≤ (21069440989159/100000000000000 : ℝ)^17 := by
    have hnat : (708632423 : ℕ)^21*100000000000000^17 ≤ 21069440989159^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708632423 2500000000 21069440989159 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1773358381/10000000000 : ℝ)^21 ≤ (11804368264129/100000000000000 : ℝ)^17 := by
    have hnat : (1773358381 : ℕ)^21*100000000000000^17 ≤ 11804368264129^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773358381 10000000000 11804368264129 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(724210729/1000000000 : ℝ), (708632423/2500000000 : ℝ), (1773358381/10000000000 : ℝ)] ![(16781547683329/25000000000000 : ℝ), (21069440989159/100000000000000 : ℝ), (11804368264129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(724210729/1000000000 : ℝ)|^21 ≤ (16781547683329/25000000000000 : ℝ)^17
        have hw : |(724210729/1000000000 : ℝ)|=(724210729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708632423/2500000000 : ℝ)|^21 ≤ (21069440989159/100000000000000 : ℝ)^17
        have hw : |(708632423/2500000000 : ℝ)|=(708632423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1773358381/10000000000 : ℝ)|^21 ≤ (11804368264129/100000000000000 : ℝ)^17
        have hw : |(1773358381/10000000000 : ℝ)|=(1773358381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-4957745359/10000000000 : ℝ)*x 0 + (203172373/1000000000 : ℝ)*x 1 + (2572549063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4957745359/10000000000 : ℝ)^21 ≤ (4203261262093/10000000000000 : ℝ)^17 := by
    have hnat : (4957745359 : ℕ)^21*10000000000000^17 ≤ 4203261262093^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4957745359 10000000000 4203261262093 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203172373/1000000000 : ℝ)^21 ≤ (13963981903627/100000000000000 : ℝ)^17 := by
    have hnat : (203172373 : ℕ)^21*100000000000000^17 ≤ 13963981903627^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203172373 1000000000 13963981903627 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2572549063/5000000000 : ℝ)^21 ≤ (44003405467223/100000000000000 : ℝ)^17 := by
    have hnat : (2572549063 : ℕ)^21*100000000000000^17 ≤ 44003405467223^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572549063 5000000000 44003405467223 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4957745359/10000000000 : ℝ), (203172373/1000000000 : ℝ), (2572549063/5000000000 : ℝ)] ![(4203261262093/10000000000000 : ℝ), (13963981903627/100000000000000 : ℝ), (44003405467223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4957745359/10000000000 : ℝ)|^21 ≤ (4203261262093/10000000000000 : ℝ)^17
        have hw : |(-4957745359/10000000000 : ℝ)|=(4957745359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203172373/1000000000 : ℝ)|^21 ≤ (13963981903627/100000000000000 : ℝ)^17
        have hw : |(203172373/1000000000 : ℝ)|=(203172373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2572549063/5000000000 : ℝ)|^21 ≤ (44003405467223/100000000000000 : ℝ)^17
        have hw : |(2572549063/5000000000 : ℝ)|=(2572549063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (149757861/5000000000 : ℝ)*x 0 + (-2332963409/5000000000 : ℝ)*x 1 + (3292742643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149757861/5000000000 : ℝ)^21 ≤ (1311988788503/100000000000000 : ℝ)^17 := by
    have hnat : (149757861 : ℕ)^21*100000000000000^17 ≤ 1311988788503^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149757861 5000000000 1311988788503 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2332963409/5000000000 : ℝ)^21 ≤ (38997876855737/100000000000000 : ℝ)^17 := by
    have hnat : (2332963409 : ℕ)^21*100000000000000^17 ≤ 38997876855737^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332963409 5000000000 38997876855737 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3292742643/5000000000 : ℝ)^21 ≤ (59690134348443/100000000000000 : ℝ)^17 := by
    have hnat : (3292742643 : ℕ)^21*100000000000000^17 ≤ 59690134348443^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3292742643 5000000000 59690134348443 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(149757861/5000000000 : ℝ), (-2332963409/5000000000 : ℝ), (3292742643/5000000000 : ℝ)] ![(1311988788503/100000000000000 : ℝ), (38997876855737/100000000000000 : ℝ), (59690134348443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(149757861/5000000000 : ℝ)|^21 ≤ (1311988788503/100000000000000 : ℝ)^17
        have hw : |(149757861/5000000000 : ℝ)|=(149757861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2332963409/5000000000 : ℝ)|^21 ≤ (38997876855737/100000000000000 : ℝ)^17
        have hw : |(-2332963409/5000000000 : ℝ)|=(2332963409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3292742643/5000000000 : ℝ)|^21 ≤ (59690134348443/100000000000000 : ℝ)^17
        have hw : |(3292742643/5000000000 : ℝ)|=(3292742643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1532216697/2500000000 : ℝ)*x 0 + (5274628937/10000000000 : ℝ)*x 1 + (1392381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1532216697/2500000000 : ℝ)^21 ≤ (2731001846957/5000000000000 : ℝ)^17 := by
    have hnat : (1532216697 : ℕ)^21*5000000000000^17 ≤ 2731001846957^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532216697 2500000000 2731001846957 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274628937/10000000000 : ℝ)^21 ≤ (45375905459133/100000000000000 : ℝ)^17 := by
    have hnat : (5274628937 : ℕ)^21*100000000000000^17 ≤ 45375905459133^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274628937 10000000000 45375905459133 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392381/5000000000 : ℝ)^21 ≤ (811517013/20000000000000 : ℝ)^17 := by
    have hnat : (1392381 : ℕ)^21*20000000000000^17 ≤ 811517013^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392381 5000000000 811517013 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1532216697/2500000000 : ℝ), (5274628937/10000000000 : ℝ), (1392381/5000000000 : ℝ)] ![(2731001846957/5000000000000 : ℝ), (45375905459133/100000000000000 : ℝ), (811517013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1532216697/2500000000 : ℝ)|^21 ≤ (2731001846957/5000000000000 : ℝ)^17
        have hw : |(1532216697/2500000000 : ℝ)|=(1532216697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274628937/10000000000 : ℝ)|^21 ≤ (45375905459133/100000000000000 : ℝ)^17
        have hw : |(5274628937/10000000000 : ℝ)|=(5274628937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1392381/5000000000 : ℝ)|^21 ≤ (811517013/20000000000000 : ℝ)^17
        have hw : |(1392381/5000000000 : ℝ)|=(1392381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s0_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (957231667/5000000000 : ℝ)*x 0 + (5274628937/10000000000 : ℝ)*x 1 + (153783327/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957231667/5000000000 : ℝ)^21 ≤ (12975286258643/100000000000000 : ℝ)^17 := by
    have hnat : (957231667 : ℕ)^21*100000000000000^17 ≤ 12975286258643^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957231667 5000000000 12975286258643 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274628937/10000000000 : ℝ)^21 ≤ (45375905459133/100000000000000 : ℝ)^17 := by
    have hnat : (5274628937 : ℕ)^21*100000000000000^17 ≤ 45375905459133^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274628937 10000000000 45375905459133 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153783327/312500000 : ℝ)^21 ≤ (416488082643/1000000000000 : ℝ)^17 := by
    have hnat : (153783327 : ℕ)^21*1000000000000^17 ≤ 416488082643^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153783327 312500000 416488082643 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(957231667/5000000000 : ℝ), (5274628937/10000000000 : ℝ), (153783327/312500000 : ℝ)] ![(12975286258643/100000000000000 : ℝ), (45375905459133/100000000000000 : ℝ), (416488082643/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(957231667/5000000000 : ℝ)|^21 ≤ (12975286258643/100000000000000 : ℝ)^17
        have hw : |(957231667/5000000000 : ℝ)|=(957231667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274628937/10000000000 : ℝ)|^21 ≤ (45375905459133/100000000000000 : ℝ)^17
        have hw : |(5274628937/10000000000 : ℝ)|=(5274628937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153783327/312500000 : ℝ)|^21 ≤ (416488082643/1000000000000 : ℝ)^17
        have hw : |(153783327/312500000 : ℝ)|=(153783327/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1622489541/5000000000 : ℝ)*x 0 + (3241853817/10000000000 : ℝ)*x 1 + (2863433111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1622489541/5000000000 : ℝ)^21 ≤ (12450102919477/50000000000000 : ℝ)^17 := by
    have hnat : (1622489541 : ℕ)^21*50000000000000^17 ≤ 12450102919477^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1622489541 5000000000 12450102919477 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3241853817/10000000000 : ℝ)^21 ≤ (4974116977097/20000000000000 : ℝ)^17 := by
    have hnat : (3241853817 : ℕ)^21*20000000000000^17 ≤ 4974116977097^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241853817 10000000000 4974116977097 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2863433111/5000000000 : ℝ)^21 ≤ (6278651158551/12500000000000 : ℝ)^17 := by
    have hnat : (2863433111 : ℕ)^21*12500000000000^17 ≤ 6278651158551^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2863433111 5000000000 6278651158551 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1622489541/5000000000 : ℝ), (3241853817/10000000000 : ℝ), (2863433111/5000000000 : ℝ)] ![(12450102919477/50000000000000 : ℝ), (4974116977097/20000000000000 : ℝ), (6278651158551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1622489541/5000000000 : ℝ)|^21 ≤ (12450102919477/50000000000000 : ℝ)^17
        have hw : |(-1622489541/5000000000 : ℝ)|=(1622489541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3241853817/10000000000 : ℝ)|^21 ≤ (4974116977097/20000000000000 : ℝ)^17
        have hw : |(3241853817/10000000000 : ℝ)|=(3241853817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2863433111/5000000000 : ℝ)|^21 ≤ (6278651158551/12500000000000 : ℝ)^17
        have hw : |(2863433111/5000000000 : ℝ)|=(2863433111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3242145209/10000000000 : ℝ)*x 0 + (-3239022673/10000000000 : ℝ)*x 1 + (2865910447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3242145209/10000000000 : ℝ)^21 ≤ (777292074569/3125000000000 : ℝ)^17 := by
    have hnat : (3242145209 : ℕ)^21*3125000000000^17 ≤ 777292074569^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242145209 10000000000 777292074569 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3239022673/10000000000 : ℝ)^21 ≤ (24843757381303/100000000000000 : ℝ)^17 := by
    have hnat : (3239022673 : ℕ)^21*100000000000000^17 ≤ 24843757381303^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3239022673 10000000000 24843757381303 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2865910447/5000000000 : ℝ)^21 ≤ (25141448112049/50000000000000 : ℝ)^17 := by
    have hnat : (2865910447 : ℕ)^21*50000000000000^17 ≤ 25141448112049^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2865910447 5000000000 25141448112049 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3242145209/10000000000 : ℝ), (-3239022673/10000000000 : ℝ), (2865910447/5000000000 : ℝ)] ![(777292074569/3125000000000 : ℝ), (24843757381303/100000000000000 : ℝ), (25141448112049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3242145209/10000000000 : ℝ)|^21 ≤ (777292074569/3125000000000 : ℝ)^17
        have hw : |(3242145209/10000000000 : ℝ)|=(3242145209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3239022673/10000000000 : ℝ)|^21 ≤ (24843757381303/100000000000000 : ℝ)^17
        have hw : |(-3239022673/10000000000 : ℝ)|=(3239022673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2865910447/5000000000 : ℝ)|^21 ≤ (25141448112049/50000000000000 : ℝ)^17
        have hw : |(2865910447/5000000000 : ℝ)|=(2865910447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1100932871/2000000000 : ℝ)*x 0 + (688697011/1250000000 : ℝ)*x 1 + (-780276983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100932871/2000000000 : ℝ)^21 ≤ (23916429277867/50000000000000 : ℝ)^17 := by
    have hnat : (1100932871 : ℕ)^21*50000000000000^17 ≤ 23916429277867^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100932871 2000000000 23916429277867 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688697011/1250000000 : ℝ)^21 ≤ (47885587150059/100000000000000 : ℝ)^17 := by
    have hnat : (688697011 : ℕ)^21*100000000000000^17 ≤ 47885587150059^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688697011 1250000000 47885587150059 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780276983/10000000000 : ℝ)^21 ≤ (4281554277499/100000000000000 : ℝ)^17 := by
    have hnat : (780276983 : ℕ)^21*100000000000000^17 ≤ 4281554277499^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780276983 10000000000 4281554277499 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100932871/2000000000 : ℝ), (688697011/1250000000 : ℝ), (-780276983/10000000000 : ℝ)] ![(23916429277867/50000000000000 : ℝ), (47885587150059/100000000000000 : ℝ), (4281554277499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100932871/2000000000 : ℝ)|^21 ≤ (23916429277867/50000000000000 : ℝ)^17
        have hw : |(1100932871/2000000000 : ℝ)|=(1100932871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688697011/1250000000 : ℝ)|^21 ≤ (47885587150059/100000000000000 : ℝ)^17
        have hw : |(688697011/1250000000 : ℝ)|=(688697011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-780276983/10000000000 : ℝ)|^21 ≤ (4281554277499/100000000000000 : ℝ)^17
        have hw : |(-780276983/10000000000 : ℝ)|=(780276983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323057_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4343565487/10000000000 : ℝ)*x 0 + (1086860297/2500000000 : ℝ)*x 1 + (906652863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343565487/10000000000 : ℝ)^21 ≤ (8924291846933/25000000000000 : ℝ)^17 := by
    have hnat : (4343565487 : ℕ)^21*25000000000000^17 ≤ 8924291846933^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343565487 10000000000 8924291846933 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086860297/2500000000 : ℝ)^21 ≤ (35736518190599/100000000000000 : ℝ)^17 := by
    have hnat : (1086860297 : ℕ)^21*100000000000000^17 ≤ 35736518190599^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086860297 2500000000 35736518190599 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906652863/2500000000 : ℝ)^21 ≤ (28566314406983/100000000000000 : ℝ)^17 := by
    have hnat : (906652863 : ℕ)^21*100000000000000^17 ≤ 28566314406983^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906652863 2500000000 28566314406983 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343565487/10000000000 : ℝ), (1086860297/2500000000 : ℝ), (906652863/2500000000 : ℝ)] ![(8924291846933/25000000000000 : ℝ), (35736518190599/100000000000000 : ℝ), (28566314406983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343565487/10000000000 : ℝ)|^21 ≤ (8924291846933/25000000000000 : ℝ)^17
        have hw : |(4343565487/10000000000 : ℝ)|=(4343565487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086860297/2500000000 : ℝ)|^21 ≤ (35736518190599/100000000000000 : ℝ)^17
        have hw : |(1086860297/2500000000 : ℝ)|=(1086860297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906652863/2500000000 : ℝ)|^21 ≤ (28566314406983/100000000000000 : ℝ)^17
        have hw : |(906652863/2500000000 : ℝ)|=(906652863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323057 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]]) : False := by
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
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(285913930952523/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2946068077/10000000000 : ℝ)*X 0 0+(2946068489/10000000000 : ℝ)*X 0 1+(6236139733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2946068077/10000000000 : ℝ)*X 1 0+(-2946068489/10000000000 : ℝ)*X 1 1+(6236139733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((22822807/40000000 : ℝ)*X 2 0+(1426425337/2500000000 : ℝ)*X 2 1+(-61/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2309038823/10000000000 : ℝ)*X 0 0+(32759733/500000000 : ℝ)*X 0 1+(4181896121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1598148727/10000000000 : ℝ)*X 1 0+(-1477880257/10000000000 : ℝ)*X 1 1+(8363791993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((453457097/1250000000 : ℝ)*X 2 0+(7615144531/10000000000 : ℝ)*X 2 1+(-572801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((592425913/2500000000 : ℝ)*X 0 0+(7615144531/10000000000 : ℝ)*X 0 1+(1759393403/10000000000 : ℝ)*X 0 2+(592425913/2500000000 : ℝ)*X 1 0+(7615144531/10000000000 : ℝ)*X 1 1+(1759393403/10000000000 : ℝ)*X 1 2+(592425913/2500000000 : ℝ)*X 2 0+(7615144531/10000000000 : ℝ)*X 2 1+(1759393403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-9976481/78125000 : ℝ)*X 0 0+(432277073/2500000000 : ℝ)*X 0 1+(8405605969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((193972613/2500000000 : ℝ)*X 1 0+(-539912237/2500000000 : ℝ)*X 1 1+(1681121141/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7972080431/10000000000 : ℝ)*X 2 0+(3194069961/10000000000 : ℝ)*X 2 1+(-282313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((724210729/1000000000 : ℝ)*X 0 0+(708632423/2500000000 : ℝ)*X 0 1+(1773358381/10000000000 : ℝ)*X 0 2+(724210729/1000000000 : ℝ)*X 1 0+(708632423/2500000000 : ℝ)*X 1 1+(1773358381/10000000000 : ℝ)*X 1 2+(724210729/1000000000 : ℝ)*X 2 0+(708632423/2500000000 : ℝ)*X 2 1+(1773358381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4957745359/10000000000 : ℝ)*X 0 0+(203172373/1000000000 : ℝ)*X 0 1+(2572549063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((149757861/5000000000 : ℝ)*X 1 0+(-2332963409/5000000000 : ℝ)*X 1 1+(3292742643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1532216697/2500000000 : ℝ)*X 2 0+(5274628937/10000000000 : ℝ)*X 2 1+(1392381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((957231667/5000000000 : ℝ)*X 0 0+(5274628937/10000000000 : ℝ)*X 0 1+(153783327/312500000 : ℝ)*X 0 2+(957231667/5000000000 : ℝ)*X 1 0+(5274628937/10000000000 : ℝ)*X 1 1+(153783327/312500000 : ℝ)*X 1 2+(957231667/5000000000 : ℝ)*X 2 0+(5274628937/10000000000 : ℝ)*X 2 1+(153783327/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((69253/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69253/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (50182514684908899/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (18124132743/62500000000 : ℝ)*(base5) + (58091005219/50000000000 : ℝ)*(base7) + (50098369721/1000000000000 : ℝ)*(base59) + (799078129011/500000000000 : ℝ)*(major_s0_0) + (799078129011/500000000000 : ℝ)*(major_s0_1) + (799078129011/500000000000 : ℝ)*(major_s0_2) + (465877/200000000000 : ℝ)*(sp_s0_0) + (245531/100000000000 : ℝ)*(sp_s0_1) + (1733108797747/1000000000000 : ℝ)*(sp_s0_7) + (866545971781/500000000000 : ℝ)*(sp_s0_8) + (404619998993/200000000000 : ℝ)*(sp_s0_9) + (844372641621/500000000000 : ℝ)*(sp_s0_13) + (548789/200000000000 : ℝ)*(sp_s0_14) + (4868051/250000000000 : ℝ)*(sp_s0_15) + (3267645211/4000000000 : ℝ)*(f.failure) + (1733113871077/1000000000000 : ℝ)*(f.sum) + (131920201/5000000000000000000000 : ℝ)*base63 + (1226456815880083/5000000000000000000000000000 : ℝ)*base64 + (516400652619917/5000000000000000000000000000 : ℝ)*base66 + (129572046455247/1000000000000000000000000000 : ℝ)*base69 + (1058029722828159/2500000000000000000000000000 : ℝ)*base70 + (3076392131380083/5000000000000000000000000000 : ℝ)*base73 + (53326647544753/1000000000000000000000000000 : ℝ)*base75 + (101366318244753/1000000000000000000000000000 : ℝ)*base77 + (62980437869917/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (13/200000000000000 : ℝ)*base86 + (13/200000000000000 : ℝ)*base88 + (13/200000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6883/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6883/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43012987356249264659769/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78465012593/250000000000 : ℝ)*(base5) + (1159153365047/1000000000000 : ℝ)*(base7) + (11989/125000000000 : ℝ)*(base40) + (22164074319/1000000000000 : ℝ)*(base60) + (786756353047/500000000000 : ℝ)*(major_s0_0) + (786756353047/500000000000 : ℝ)*(major_s0_1) + (786756353047/500000000000 : ℝ)*(major_s0_2) + (97353/15625000000 : ℝ)*(sp_s0_0) + (7644951/1000000000000 : ℝ)*(sp_s0_1) + (6116473/100000000000 : ℝ)*(sp_s0_7) + (1697835499979/1000000000000 : ℝ)*(sp_s0_14) + (33957905007/20000000000 : ℝ)*(sp_s0_15) + (2011762945673/1000000000000 : ℝ)*(sp_s0_16) + (1649607854117/1000000000000 : ℝ)*(sp_s0_20) + (804314539443/1000000000000 : ℝ)*(f.failure) + (1697902895301/1000000000000 : ℝ)*(f.sum) + (1406332629/2500000000000000000000 : ℝ)*base63 + (1247695191483991/5000000000000000000000000000 : ℝ)*base64 + (707025280516009/5000000000000000000000000000 : ℝ)*base66 + (382413580912419/1000000000000000000000000000 : ℝ)*base69 + (1100615638523043/2500000000000000000000000000 : ℝ)*base70 + (852937926483991/5000000000000000000000000000 : ℝ)*base73 + (276602584087581/1000000000000000000000000000 : ℝ)*base75 + (265750688312419/1000000000000000000000000000 : ℝ)*base76 + (1071247311733991/2500000000000000000000000000 : ℝ)*base79 + (4069/50000000000000000 : ℝ)*base86 + (4069/50000000000000000 : ℝ)*base88 + (4069/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6093/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6093/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34039985315658702186189/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216389334197/200000000000 : ℝ)*(base5) + (114902076897/250000000000 : ℝ)*(base7) + (147609/500000000000 : ℝ)*(base8) + (4165721/1000000000000 : ℝ)*(base40) + (22522754029/100000000000 : ℝ)*(base50) + (394762818093/500000000000 : ℝ)*(base59) + (1221955764493/1000000000000 : ℝ)*(major_s0_0) + (1221955764493/1000000000000 : ℝ)*(major_s0_1) + (1221955764493/1000000000000 : ℝ)*(major_s0_2) + (17323053/200000000000 : ℝ)*(sp_s0_2) + (1563629463021/1000000000000 : ℝ)*(sp_s0_21) + (9772685989/6250000000 : ℝ)*(sp_s0_22) + (2645489813959/1000000000000 : ℝ)*(sp_s0_23) + (1137412373/500000000000 : ℝ)*(sp_s0_27) + (39038324259/62500000000 : ℝ)*(f.failure) + (9772685989/6250000000 : ℝ)*(f.sum) + (4256051/80000000000000000000 : ℝ)*base63 + (4415618361304371/10000000000000000000000000000 : ℝ)*base65 + (54601516695629/10000000000000000000000000000 : ℝ)*base67 + (224559359034161/2000000000000000000000000000 : ℝ)*base69 + (3828288886066783/5000000000000000000000000000 : ℝ)*base71 + (3469256477304371/10000000000000000000000000000 : ℝ)*base72 + (1850264030965839/2000000000000000000000000000 : ℝ)*base75 + (1686841391165839/2000000000000000000000000000 : ℝ)*base77 + (2711321561804371/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (989/1562500000000000 : ℝ)*base87 + (989/1562500000000000 : ℝ)*base89 + (989/1562500000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (69253/100000 : ℝ) ^ (83/16 : ℝ) ≤ (929298445993826701/6250000000000000000 : ℝ) := by
    have hpowers : (69253/100000 : ℝ)^83 ≤ (929298445993826701/6250000000000000000 : ℝ)^16 := by
      have hnat : (69253 : ℕ)^83*6250000000000000000^16 ≤ 929298445993826701^16*100000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69253 100000 929298445993826701 6250000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69253/100000 : ℝ)) (X := (929298445993826701/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (7179298445993826701/6250000000000000000 : ℝ) ≤ (256770550141181/250000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (7179298445993826701/6250000000000000000 : ℝ)^16 ≤ (256770550141181/250000000000000 : ℝ)^83 := by
      have hnat : (7179298445993826701 : ℕ)^16*250000000000000^83 ≤ 256770550141181^83*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7179298445993826701 6250000000000000000 256770550141181 250000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (256770550141181/250000000000000 : ℝ)) (X := (7179298445993826701/6250000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (4054298445993826701/3125000000000000000 : ℝ) ≤ (420586944552303/400000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (4054298445993826701/3125000000000000000 : ℝ)^16 ≤ (420586944552303/400000000000000 : ℝ)^83 := by
      have hnat : (4054298445993826701 : ℕ)^16*400000000000000^83 ≤ 420586944552303^83*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4054298445993826701 3125000000000000000 420586944552303 400000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (420586944552303/400000000000000 : ℝ)) (X := (4054298445993826701/3125000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6770550141181/173132500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(48770321632067/1385060000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (69253/100000 : ℝ)) (alpha := (6770550141181/173132500000000 : ℝ)) (beta := (48770321632067/1385060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (69253/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6770550141181/173132500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(48770321632067/1385060000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6883/10000 : ℝ) ^ (83/16 : ℝ) ≤ (14403637391304344409/100000000000000000000 : ℝ) := by
    have hpowers : (6883/10000 : ℝ)^83 ≤ (14403637391304344409/100000000000000000000 : ℝ)^16 := by
      have hnat : (6883 : ℕ)^83*100000000000000000000^16 ≤ 14403637391304344409^16*10000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6883 10000 14403637391304344409 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6883/10000 : ℝ)) (X := (14403637391304344409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (114403637391304344409/100000000000000000000 : ℝ) ≤ (5131395798637769/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (114403637391304344409/100000000000000000000 : ℝ)^16 ≤ (5131395798637769/5000000000000000 : ℝ)^83 := by
      have hnat : (114403637391304344409 : ℕ)^16*5000000000000000^83 ≤ 5131395798637769^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114403637391304344409 100000000000000000000 5131395798637769 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5131395798637769/5000000000000000 : ℝ)) (X := (114403637391304344409/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (64403637391304344409/50000000000000000000 : ℝ) ≤ (656256088850433/625000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (64403637391304344409/50000000000000000000 : ℝ)^16 ≤ (656256088850433/625000000000000 : ℝ)^83 := by
      have hnat : (64403637391304344409 : ℕ)^16*625000000000000^83 ≤ 656256088850433^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64403637391304344409 50000000000000000000 656256088850433 625000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (656256088850433/625000000000000 : ℝ)) (X := (64403637391304344409/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(131395798637769/3441500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(23730582433139/688300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (6883/10000 : ℝ)) (alpha := (131395798637769/3441500000000000 : ℝ)) (beta := (23730582433139/688300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6883/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(131395798637769/3441500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(23730582433139/688300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (6093/20000 : ℝ) ^ (83/16 : ℝ) ≤ (41999936102746329/20000000000000000000 : ℝ) := by
    have hpowers : (6093/20000 : ℝ)^83 ≤ (41999936102746329/20000000000000000000 : ℝ)^16 := by
      have hnat : (6093 : ℕ)^83*20000000000000000000^16 ≤ 41999936102746329^16*20000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6093 20000 41999936102746329 20000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6093/20000 : ℝ)) (X := (41999936102746329/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20041999936102746329/20000000000000000000 : ℝ) ≤ (10004044759747859/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (20041999936102746329/20000000000000000000 : ℝ)^16 ≤ (10004044759747859/10000000000000000 : ℝ)^83 := by
      have hnat : (20041999936102746329 : ℕ)^16*10000000000000000^83 ≤ 10004044759747859^83*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20041999936102746329 20000000000000000000 10004044759747859 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004044759747859/10000000000000000 : ℝ)) (X := (20041999936102746329/20000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10041999936102746329/10000000000000000000 : ℝ) ≤ (10008082683052993/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (10041999936102746329/10000000000000000000 : ℝ)^16 ≤ (10008082683052993/10000000000000000 : ℝ)^83 := by
      have hnat : (10041999936102746329 : ℕ)^16*10000000000000000^83 ≤ 10008082683052993^83*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10041999936102746329 10000000000000000000 10008082683052993 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008082683052993/10000000000000000 : ℝ)) (X := (10041999936102746329/10000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4044759747859/3046500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2018961652567/1523250000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (6093/20000 : ℝ)) (alpha := (4044759747859/3046500000000000 : ℝ)) (beta := (2018961652567/1523250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6093/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4044759747859/3046500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2018961652567/1523250000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1622489541/5000000000 : ℝ)*X 0 0+(3241853817/10000000000 : ℝ)*X 0 1+(2863433111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3242145209/10000000000 : ℝ)*X 1 0+(-3239022673/10000000000 : ℝ)*X 1 1+(2865910447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1100932871/2000000000 : ℝ)*X 2 0+(688697011/1250000000 : ℝ)*X 2 1+(-780276983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4343565487/10000000000 : ℝ)*X 0 0+(1086860297/2500000000 : ℝ)*X 0 1+(906652863/2500000000 : ℝ)*X 0 2+(4343565487/10000000000 : ℝ)*X 1 0+(1086860297/2500000000 : ℝ)*X 1 1+(906652863/2500000000 : ℝ)*X 1 2+(4343565487/10000000000 : ℝ)*X 2 0+(1086860297/2500000000 : ℝ)*X 2 1+(906652863/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323057_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-702024543209906882117076444365114049/80676126530750000000000000000000000 : ℝ) := by norm_num
    linear_combination (48731/1000000000000 : ℝ)*(base8) + (7087/200000000000 : ℝ)*(base13) + (14687/1000000000000 : ℝ)*(base49) + (28789/1000000000000 : ℝ)*(base50) + (5073/500000000000 : ℝ)*(base53) + (144706028189/125000000000 : ℝ)*(base59) + (578973431561/1000000000000 : ℝ)*(base60) + (978170004209/500000000000 : ℝ)*(major_s1_0) + (97817/50000 : ℝ)*(major_s1_1) + (978169994927/500000000000 : ℝ)*(major_s1_2) + (2900587589991/1000000000000 : ℝ)*(sp_s1_0) + (116023507303/40000000000 : ℝ)*(sp_s1_1) + (36257346159/12500000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2900587684303/1000000000000 : ℝ)*(f.sum) + (3048840651426449731/10484529750000000000000000000000 : ℝ)*base63 + (756824446265507/1523250000000000000000000000 : ℝ)*base65 + (7164245257117/34415000000000000000000000 : ℝ)*base67 + (44482293281677/95203125000000000000000000 : ℝ)*base69 + (45496939380685301621/105489632250000000000000000000000 : ℝ)*base71 + (376618136758647/692530000000000000000000000 : ℝ)*base72 + (107064871213/172075000000000000000000 : ℝ)*base75 + (17611013391069/86566250000000000000000000 : ℝ)*base77 + (1622578306886250889/4766683990000000000000000000000 : ℝ)*base79 + (4209/500000000000 : ℝ)*base83 + (8417/1000000000000 : ℝ)*base85 + (4209/500000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p023_b032 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=57 := by omega
  rcases hc with rfl
  · exact collision_c323057 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
