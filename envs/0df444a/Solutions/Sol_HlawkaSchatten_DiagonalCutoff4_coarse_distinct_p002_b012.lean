-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b012
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:12:41.470448+00:00
-- url     : https://prove2.me/submissions/cd4517a8-dcd0-4397-ae03-91737a86fc48

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
theorem collision_support_c302025_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1382973737/2500000000 : ℝ)*x 0 + (1604678473/5000000000 : ℝ)*x 1 + (4159691273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1382973737/2500000000 : ℝ)^67 ≤ (22970842512447/50000000000000 : ℝ)^51 := by
    have hnat : (1382973737 : ℕ)^67*50000000000000^51 ≤ 22970842512447^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382973737 2500000000 22970842512447 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1604678473/5000000000 : ℝ)^67 ≤ (22468225514281/100000000000000 : ℝ)^51 := by
    have hnat : (1604678473 : ℕ)^67*100000000000000^51 ≤ 22468225514281^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604678473 5000000000 22468225514281 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159691273/10000000000 : ℝ)^67 ≤ (31590089446437/100000000000000 : ℝ)^51 := by
    have hnat : (4159691273 : ℕ)^67*100000000000000^51 ≤ 31590089446437^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159691273 10000000000 31590089446437 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1382973737/2500000000 : ℝ), (1604678473/5000000000 : ℝ), (4159691273/10000000000 : ℝ)] ![(22970842512447/50000000000000 : ℝ), (22468225514281/100000000000000 : ℝ), (31590089446437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1382973737/2500000000 : ℝ)|^67 ≤ (22970842512447/50000000000000 : ℝ)^51
        have hw : |(-1382973737/2500000000 : ℝ)|=(1382973737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1604678473/5000000000 : ℝ)|^67 ≤ (22468225514281/100000000000000 : ℝ)^51
        have hw : |(1604678473/5000000000 : ℝ)|=(1604678473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159691273/10000000000 : ℝ)|^67 ≤ (31590089446437/100000000000000 : ℝ)^51
        have hw : |(4159691273/10000000000 : ℝ)|=(4159691273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (589007017/1250000000 : ℝ)*x 0 + (-85428853/312500000 : ℝ)*x 1 + (1081484041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589007017/1250000000 : ℝ)^67 ≤ (37212448421063/100000000000000 : ℝ)^51 := by
    have hnat : (589007017 : ℕ)^67*100000000000000^51 ≤ 37212448421063^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589007017 1250000000 37212448421063 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85428853/312500000 : ℝ)^67 ≤ (18199107904641/100000000000000 : ℝ)^51 := by
    have hnat : (85428853 : ℕ)^67*100000000000000^51 ≤ 18199107904641^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85428853 312500000 18199107904641 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081484041/2000000000 : ℝ)^67 ≤ (22294221832221/50000000000000 : ℝ)^51 := by
    have hnat : (1081484041 : ℕ)^67*50000000000000^51 ≤ 22294221832221^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081484041 2000000000 22294221832221 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(589007017/1250000000 : ℝ), (-85428853/312500000 : ℝ), (1081484041/2000000000 : ℝ)] ![(37212448421063/100000000000000 : ℝ), (18199107904641/100000000000000 : ℝ), (22294221832221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(589007017/1250000000 : ℝ)|^67 ≤ (37212448421063/100000000000000 : ℝ)^51
        have hw : |(589007017/1250000000 : ℝ)|=(589007017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85428853/312500000 : ℝ)|^67 ≤ (18199107904641/100000000000000 : ℝ)^51
        have hw : |(-85428853/312500000 : ℝ)|=(85428853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081484041/2000000000 : ℝ)|^67 ≤ (22294221832221/50000000000000 : ℝ)^51
        have hw : |(1081484041/2000000000 : ℝ)|=(1081484041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3478981083/10000000000 : ℝ)*x 0 + (833209177/1250000000 : ℝ)*x 1 + (-2517017363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3478981083/10000000000 : ℝ)^67 ≤ (24980083877257/100000000000000 : ℝ)^51 := by
    have hnat : (3478981083 : ℕ)^67*100000000000000^51 ≤ 24980083877257^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3478981083 10000000000 24980083877257 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833209177/1250000000 : ℝ)^67 ≤ (11738413655831/20000000000000 : ℝ)^51 := by
    have hnat : (833209177 : ℕ)^67*20000000000000^51 ≤ 11738413655831^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833209177 1250000000 11738413655831 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2517017363/10000000000 : ℝ)^67 ≤ (1020490489787/6250000000000 : ℝ)^51 := by
    have hnat : (2517017363 : ℕ)^67*6250000000000^51 ≤ 1020490489787^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517017363 10000000000 1020490489787 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3478981083/10000000000 : ℝ), (833209177/1250000000 : ℝ), (-2517017363/10000000000 : ℝ)] ![(24980083877257/100000000000000 : ℝ), (11738413655831/20000000000000 : ℝ), (1020490489787/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3478981083/10000000000 : ℝ)|^67 ≤ (24980083877257/100000000000000 : ℝ)^51
        have hw : |(3478981083/10000000000 : ℝ)|=(3478981083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833209177/1250000000 : ℝ)|^67 ≤ (11738413655831/20000000000000 : ℝ)^51
        have hw : |(833209177/1250000000 : ℝ)|=(833209177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2517017363/10000000000 : ℝ)|^67 ≤ (1020490489787/6250000000000 : ℝ)^51
        have hw : |(-2517017363/10000000000 : ℝ)|=(2517017363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1159572157/2000000000 : ℝ)*x 0 + (500902289/2000000000 : ℝ)*x 1 + (561099237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1159572157/2000000000 : ℝ)^67 ≤ (48865106801379/100000000000000 : ℝ)^51 := by
    have hnat : (1159572157 : ℕ)^67*100000000000000^51 ≤ 48865106801379^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159572157 2000000000 48865106801379 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500902289/2000000000 : ℝ)^67 ≤ (4055338532811/25000000000000 : ℝ)^51 := by
    have hnat : (500902289 : ℕ)^67*25000000000000^51 ≤ 4055338532811^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500902289 2000000000 4055338532811 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561099237/1250000000 : ℝ)^67 ≤ (8728384762589/25000000000000 : ℝ)^51 := by
    have hnat : (561099237 : ℕ)^67*25000000000000^51 ≤ 8728384762589^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561099237 1250000000 8728384762589 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1159572157/2000000000 : ℝ), (500902289/2000000000 : ℝ), (561099237/1250000000 : ℝ)] ![(48865106801379/100000000000000 : ℝ), (4055338532811/25000000000000 : ℝ), (8728384762589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1159572157/2000000000 : ℝ)|^67 ≤ (48865106801379/100000000000000 : ℝ)^51
        have hw : |(-1159572157/2000000000 : ℝ)|=(1159572157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500902289/2000000000 : ℝ)|^67 ≤ (4055338532811/25000000000000 : ℝ)^51
        have hw : |(500902289/2000000000 : ℝ)|=(500902289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561099237/1250000000 : ℝ)|^67 ≤ (8728384762589/25000000000000 : ℝ)^51
        have hw : |(561099237/1250000000 : ℝ)|=(561099237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4439751493/10000000000 : ℝ)*x 0 + (-1917846743/10000000000 : ℝ)*x 1 + (6270396379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4439751493/10000000000 : ℝ)^67 ≤ (34413281364709/100000000000000 : ℝ)^51 := by
    have hnat : (4439751493 : ℕ)^67*100000000000000^51 ≤ 34413281364709^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439751493 10000000000 34413281364709 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917846743/10000000000 : ℝ)^67 ≤ (571194928337/5000000000000 : ℝ)^51 := by
    have hnat : (1917846743 : ℕ)^67*5000000000000^51 ≤ 571194928337^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917846743 10000000000 571194928337 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6270396379/10000000000 : ℝ)^67 ≤ (10832564011899/20000000000000 : ℝ)^51 := by
    have hnat : (6270396379 : ℕ)^67*20000000000000^51 ≤ 10832564011899^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6270396379 10000000000 10832564011899 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4439751493/10000000000 : ℝ), (-1917846743/10000000000 : ℝ), (6270396379/10000000000 : ℝ)] ![(34413281364709/100000000000000 : ℝ), (571194928337/5000000000000 : ℝ), (10832564011899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4439751493/10000000000 : ℝ)|^67 ≤ (34413281364709/100000000000000 : ℝ)^51
        have hw : |(4439751493/10000000000 : ℝ)|=(4439751493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1917846743/10000000000 : ℝ)|^67 ≤ (571194928337/5000000000000 : ℝ)^51
        have hw : |(-1917846743/10000000000 : ℝ)|=(1917846743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6270396379/10000000000 : ℝ)|^67 ≤ (10832564011899/20000000000000 : ℝ)^51
        have hw : |(6270396379/10000000000 : ℝ)|=(6270396379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (549424271/2000000000 : ℝ)*x 0 + (3763282897/5000000000 : ℝ)*x 1 + (-2095896471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549424271/2000000000 : ℝ)^67 ≤ (2289546850361/12500000000000 : ℝ)^51 := by
    have hnat : (549424271 : ℕ)^67*12500000000000^51 ≤ 2289546850361^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549424271 2000000000 2289546850361 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3763282897/5000000000 : ℝ)^67 ≤ (68846545331311/100000000000000 : ℝ)^51 := by
    have hnat : (3763282897 : ℕ)^67*100000000000000^51 ≤ 68846545331311^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763282897 5000000000 68846545331311 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095896471/10000000000 : ℝ)^67 ≤ (12837079847117/100000000000000 : ℝ)^51 := by
    have hnat : (2095896471 : ℕ)^67*100000000000000^51 ≤ 12837079847117^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095896471 10000000000 12837079847117 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(549424271/2000000000 : ℝ), (3763282897/5000000000 : ℝ), (-2095896471/10000000000 : ℝ)] ![(2289546850361/12500000000000 : ℝ), (68846545331311/100000000000000 : ℝ), (12837079847117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(549424271/2000000000 : ℝ)|^67 ≤ (2289546850361/12500000000000 : ℝ)^51
        have hw : |(549424271/2000000000 : ℝ)|=(549424271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3763282897/5000000000 : ℝ)|^67 ≤ (68846545331311/100000000000000 : ℝ)^51
        have hw : |(3763282897/5000000000 : ℝ)|=(3763282897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095896471/10000000000 : ℝ)|^67 ≤ (12837079847117/100000000000000 : ℝ)^51
        have hw : |(-2095896471/10000000000 : ℝ)|=(2095896471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_12 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2239032867/10000000000 : ℝ)*x 0 + (3067252227/5000000000 : ℝ)*x 1 + (433722067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239032867/10000000000 : ℝ)^67 ≤ (7000480898953/50000000000000 : ℝ)^51 := by
    have hnat : (2239032867 : ℕ)^67*50000000000000^51 ≤ 7000480898953^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239032867 10000000000 7000480898953 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3067252227/5000000000 : ℝ)^67 ≤ (1052520339247/2000000000000 : ℝ)^51 := by
    have hnat : (3067252227 : ℕ)^67*2000000000000^51 ≤ 1052520339247^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3067252227 5000000000 1052520339247 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433722067/1000000000 : ℝ)^67 ≤ (6674604246223/20000000000000 : ℝ)^51 := by
    have hnat : (433722067 : ℕ)^67*20000000000000^51 ≤ 6674604246223^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433722067 1000000000 6674604246223 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239032867/10000000000 : ℝ), (3067252227/5000000000 : ℝ), (433722067/1000000000 : ℝ)] ![(7000480898953/50000000000000 : ℝ), (1052520339247/2000000000000 : ℝ), (6674604246223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239032867/10000000000 : ℝ)|^67 ≤ (7000480898953/50000000000000 : ℝ)^51
        have hw : |(2239032867/10000000000 : ℝ)|=(2239032867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3067252227/5000000000 : ℝ)|^67 ≤ (1052520339247/2000000000000 : ℝ)^51
        have hw : |(3067252227/5000000000 : ℝ)|=(3067252227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433722067/1000000000 : ℝ)|^67 ≤ (6674604246223/20000000000000 : ℝ)^51
        have hw : |(433722067/1000000000 : ℝ)|=(433722067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2885852859/5000000000 : ℝ)*x 0 + (2268903321/10000000000 : ℝ)*x 1 + (94173603/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2885852859/5000000000 : ℝ)^67 ≤ (48575716624687/100000000000000 : ℝ)^51 := by
    have hnat : (2885852859 : ℕ)^67*100000000000000^51 ≤ 48575716624687^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885852859 5000000000 48575716624687 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268903321/10000000000 : ℝ)^67 ≤ (14246856394783/100000000000000 : ℝ)^51 := by
    have hnat : (2268903321 : ℕ)^67*100000000000000^51 ≤ 14246856394783^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268903321 10000000000 14246856394783 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94173603/200000000 : ℝ)^67 ≤ (18588713481049/50000000000000 : ℝ)^51 := by
    have hnat : (94173603 : ℕ)^67*50000000000000^51 ≤ 18588713481049^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94173603 200000000 18588713481049 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2885852859/5000000000 : ℝ), (2268903321/10000000000 : ℝ), (94173603/200000000 : ℝ)] ![(48575716624687/100000000000000 : ℝ), (14246856394783/100000000000000 : ℝ), (18588713481049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2885852859/5000000000 : ℝ)|^67 ≤ (48575716624687/100000000000000 : ℝ)^51
        have hw : |(-2885852859/5000000000 : ℝ)|=(2885852859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2268903321/10000000000 : ℝ)|^67 ≤ (14246856394783/100000000000000 : ℝ)^51
        have hw : |(2268903321/10000000000 : ℝ)|=(2268903321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94173603/200000000 : ℝ)|^67 ≤ (18588713481049/50000000000000 : ℝ)^51
        have hw : |(94173603/200000000 : ℝ)|=(94173603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1387635039/2500000000 : ℝ)*x 0 + (-1491653027/5000000000 : ℝ)*x 1 + (2172033203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1387635039/2500000000 : ℝ)^67 ≤ (11536304435591/25000000000000 : ℝ)^51 := by
    have hnat : (1387635039 : ℕ)^67*25000000000000^51 ≤ 11536304435591^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387635039 2500000000 11536304435591 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1491653027/5000000000 : ℝ)^67 ≤ (2551567931297/12500000000000 : ℝ)^51 := by
    have hnat : (1491653027 : ℕ)^67*12500000000000^51 ≤ 2551567931297^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491653027 5000000000 2551567931297 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172033203/5000000000 : ℝ)^67 ≤ (33442238785907/100000000000000 : ℝ)^51 := by
    have hnat : (2172033203 : ℕ)^67*100000000000000^51 ≤ 33442238785907^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172033203 5000000000 33442238785907 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1387635039/2500000000 : ℝ), (-1491653027/5000000000 : ℝ), (2172033203/5000000000 : ℝ)] ![(11536304435591/25000000000000 : ℝ), (2551567931297/12500000000000 : ℝ), (33442238785907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1387635039/2500000000 : ℝ)|^67 ≤ (11536304435591/25000000000000 : ℝ)^51
        have hw : |(1387635039/2500000000 : ℝ)|=(1387635039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1491653027/5000000000 : ℝ)|^67 ≤ (2551567931297/12500000000000 : ℝ)^51
        have hw : |(-1491653027/5000000000 : ℝ)|=(1491653027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2172033203/5000000000 : ℝ)|^67 ≤ (33442238785907/100000000000000 : ℝ)^51
        have hw : |(2172033203/5000000000 : ℝ)|=(2172033203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3148416923/10000000000 : ℝ)*x 0 + (3519516019/5000000000 : ℝ)*x 1 + (-2364691131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3148416923/10000000000 : ℝ)^67 ≤ (21909424977649/100000000000000 : ℝ)^51 := by
    have hnat : (3148416923 : ℕ)^67*100000000000000^51 ≤ 21909424977649^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3148416923 10000000000 21909424977649 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3519516019/5000000000 : ℝ)^67 ≤ (31524185121117/50000000000000 : ℝ)^51 := by
    have hnat : (3519516019 : ℕ)^67*50000000000000^51 ≤ 31524185121117^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3519516019 5000000000 31524185121117 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364691131/10000000000 : ℝ)^67 ≤ (601688190513/4000000000000 : ℝ)^51 := by
    have hnat : (2364691131 : ℕ)^67*4000000000000^51 ≤ 601688190513^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364691131 10000000000 601688190513 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3148416923/10000000000 : ℝ), (3519516019/5000000000 : ℝ), (-2364691131/10000000000 : ℝ)] ![(21909424977649/100000000000000 : ℝ), (31524185121117/50000000000000 : ℝ), (601688190513/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3148416923/10000000000 : ℝ)|^67 ≤ (21909424977649/100000000000000 : ℝ)^51
        have hw : |(3148416923/10000000000 : ℝ)|=(3148416923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3519516019/5000000000 : ℝ)|^67 ≤ (31524185121117/50000000000000 : ℝ)^51
        have hw : |(3519516019/5000000000 : ℝ)|=(3519516019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2364691131/10000000000 : ℝ)|^67 ≤ (601688190513/4000000000000 : ℝ)^51
        have hw : |(-2364691131/10000000000 : ℝ)|=(2364691131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_19 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (226578487/2000000000 : ℝ)*x 0 + (3944863493/10000000000 : ℝ)*x 1 + (7188649279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226578487/2000000000 : ℝ)^67 ≤ (22883557809/400000000000 : ℝ)^51 := by
    have hnat : (226578487 : ℕ)^67*400000000000^51 ≤ 22883557809^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226578487 2000000000 22883557809 400000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3944863493/10000000000 : ℝ)^67 ≤ (1841522085369/6250000000000 : ℝ)^51 := by
    have hnat : (3944863493 : ℕ)^67*6250000000000^51 ≤ 1841522085369^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3944863493 10000000000 1841522085369 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7188649279/10000000000 : ℝ)^67 ≤ (64814757169157/100000000000000 : ℝ)^51 := by
    have hnat : (7188649279 : ℕ)^67*100000000000000^51 ≤ 64814757169157^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7188649279 10000000000 64814757169157 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(226578487/2000000000 : ℝ), (3944863493/10000000000 : ℝ), (7188649279/10000000000 : ℝ)] ![(22883557809/400000000000 : ℝ), (1841522085369/6250000000000 : ℝ), (64814757169157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(226578487/2000000000 : ℝ)|^67 ≤ (22883557809/400000000000 : ℝ)^51
        have hw : |(226578487/2000000000 : ℝ)|=(226578487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3944863493/10000000000 : ℝ)|^67 ≤ (1841522085369/6250000000000 : ℝ)^51
        have hw : |(3944863493/10000000000 : ℝ)|=(3944863493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7188649279/10000000000 : ℝ)|^67 ≤ (64814757169157/100000000000000 : ℝ)^51
        have hw : |(7188649279/10000000000 : ℝ)|=(7188649279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-6325956599/10000000000 : ℝ)*x 0 + (2418452091/10000000000 : ℝ)*x 1 + (992538253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6325956599/10000000000 : ℝ)^67 ≤ (13698544938387/25000000000000 : ℝ)^51 := by
    have hnat : (6325956599 : ℕ)^67*25000000000000^51 ≤ 13698544938387^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6325956599 10000000000 13698544938387 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418452091/10000000000 : ℝ)^67 ≤ (15493070065849/100000000000000 : ℝ)^51 := by
    have hnat : (2418452091 : ℕ)^67*100000000000000^51 ≤ 15493070065849^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418452091 10000000000 15493070065849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992538253/2500000000 : ℝ)^67 ≤ (29712750169383/100000000000000 : ℝ)^51 := by
    have hnat : (992538253 : ℕ)^67*100000000000000^51 ≤ 29712750169383^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992538253 2500000000 29712750169383 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6325956599/10000000000 : ℝ), (2418452091/10000000000 : ℝ), (992538253/2500000000 : ℝ)] ![(13698544938387/25000000000000 : ℝ), (15493070065849/100000000000000 : ℝ), (29712750169383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6325956599/10000000000 : ℝ)|^67 ≤ (13698544938387/25000000000000 : ℝ)^51
        have hw : |(-6325956599/10000000000 : ℝ)|=(6325956599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418452091/10000000000 : ℝ)|^67 ≤ (15493070065849/100000000000000 : ℝ)^51
        have hw : |(2418452091/10000000000 : ℝ)|=(2418452091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(992538253/2500000000 : ℝ)|^67 ≤ (29712750169383/100000000000000 : ℝ)^51
        have hw : |(992538253/2500000000 : ℝ)|=(992538253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (393348263/1000000000 : ℝ)*x 0 + (-1851635599/5000000000 : ℝ)*x 1 + (1061893583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393348263/1000000000 : ℝ)^67 ≤ (14676365908579/50000000000000 : ℝ)^51 := by
    have hnat : (393348263 : ℕ)^67*50000000000000^51 ≤ 14676365908579^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393348263 1000000000 14676365908579 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1851635599/5000000000 : ℝ)^67 ≤ (27116884884301/100000000000000 : ℝ)^51 := by
    have hnat : (1851635599 : ℕ)^67*100000000000000^51 ≤ 27116884884301^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851635599 5000000000 27116884884301 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061893583/2000000000 : ℝ)^67 ≤ (21765191642277/50000000000000 : ℝ)^51 := by
    have hnat : (1061893583 : ℕ)^67*50000000000000^51 ≤ 21765191642277^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061893583 2000000000 21765191642277 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(393348263/1000000000 : ℝ), (-1851635599/5000000000 : ℝ), (1061893583/2000000000 : ℝ)] ![(14676365908579/50000000000000 : ℝ), (27116884884301/100000000000000 : ℝ), (21765191642277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(393348263/1000000000 : ℝ)|^67 ≤ (14676365908579/50000000000000 : ℝ)^51
        have hw : |(393348263/1000000000 : ℝ)|=(393348263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1851635599/5000000000 : ℝ)|^67 ≤ (27116884884301/100000000000000 : ℝ)^51
        have hw : |(-1851635599/5000000000 : ℝ)|=(1851635599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061893583/2000000000 : ℝ)|^67 ≤ (21765191642277/50000000000000 : ℝ)^51
        have hw : |(1061893583/2000000000 : ℝ)|=(1061893583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4163789321/10000000000 : ℝ)*x 0 + (3090373001/5000000000 : ℝ)*x 1 + (-1193042449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163789321/10000000000 : ℝ)^67 ≤ (15815490731069/50000000000000 : ℝ)^51 := by
    have hnat : (4163789321 : ℕ)^67*50000000000000^51 ≤ 15815490731069^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163789321 10000000000 15815490731069 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3090373001/5000000000 : ℝ)^67 ≤ (66434720541/125000000000 : ℝ)^51 := by
    have hnat : (3090373001 : ℕ)^67*125000000000^51 ≤ 66434720541^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3090373001 5000000000 66434720541 125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193042449/5000000000 : ℝ)^67 ≤ (380531052307/2500000000000 : ℝ)^51 := by
    have hnat : (1193042449 : ℕ)^67*2500000000000^51 ≤ 380531052307^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193042449 5000000000 380531052307 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163789321/10000000000 : ℝ), (3090373001/5000000000 : ℝ), (-1193042449/5000000000 : ℝ)] ![(15815490731069/50000000000000 : ℝ), (66434720541/125000000000 : ℝ), (380531052307/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163789321/10000000000 : ℝ)|^67 ≤ (15815490731069/50000000000000 : ℝ)^51
        have hw : |(4163789321/10000000000 : ℝ)|=(4163789321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3090373001/5000000000 : ℝ)|^67 ≤ (66434720541/125000000000 : ℝ)^51
        have hw : |(3090373001/5000000000 : ℝ)|=(3090373001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1193042449/5000000000 : ℝ)|^67 ≤ (380531052307/2500000000000 : ℝ)^51
        have hw : |(-1193042449/5000000000 : ℝ)|=(1193042449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s0_26 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4792847/39062500 : ℝ)*x 0 + (5433281999/10000000000 : ℝ)*x 1 + (1158002277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4792847/39062500 : ℝ)^67 ≤ (6352978469641/100000000000000 : ℝ)^51 := by
    have hnat : (4792847 : ℕ)^67*100000000000000^51 ≤ 6352978469641^51*39062500^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792847 39062500 6352978469641 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433281999/10000000000 : ℝ)^67 ≤ (22434403367427/50000000000000 : ℝ)^51 := by
    have hnat : (5433281999 : ℕ)^67*50000000000000^51 ≤ 22434403367427^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433281999 10000000000 22434403367427 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158002277/2000000000 : ℝ)^67 ≤ (48778214782417/100000000000000 : ℝ)^51 := by
    have hnat : (1158002277 : ℕ)^67*100000000000000^51 ≤ 48778214782417^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158002277 2000000000 48778214782417 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4792847/39062500 : ℝ), (5433281999/10000000000 : ℝ), (1158002277/2000000000 : ℝ)] ![(6352978469641/100000000000000 : ℝ), (22434403367427/50000000000000 : ℝ), (48778214782417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4792847/39062500 : ℝ)|^67 ≤ (6352978469641/100000000000000 : ℝ)^51
        have hw : |(4792847/39062500 : ℝ)|=(4792847/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433281999/10000000000 : ℝ)|^67 ≤ (22434403367427/50000000000000 : ℝ)^51
        have hw : |(5433281999/10000000000 : ℝ)|=(5433281999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1158002277/2000000000 : ℝ)|^67 ≤ (48778214782417/100000000000000 : ℝ)^51
        have hw : |(1158002277/2000000000 : ℝ)|=(1158002277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4877113997/10000000000 : ℝ)*x 0 + (1013310119/2500000000 : ℝ)*x 1 + (4053351567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4877113997/10000000000 : ℝ)^67 ≤ (38934236440443/100000000000000 : ℝ)^51 := by
    have hnat : (4877113997 : ℕ)^67*100000000000000^51 ≤ 38934236440443^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877113997 10000000000 38934236440443 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013310119/2500000000 : ℝ)^67 ≤ (3053233209339/10000000000000 : ℝ)^51 := by
    have hnat : (1013310119 : ℕ)^67*10000000000000^51 ≤ 3053233209339^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013310119 2500000000 3053233209339 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4053351567/10000000000 : ℝ)^67 ≤ (30533431461099/100000000000000 : ℝ)^51 := by
    have hnat : (4053351567 : ℕ)^67*100000000000000^51 ≤ 30533431461099^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053351567 10000000000 30533431461099 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4877113997/10000000000 : ℝ), (1013310119/2500000000 : ℝ), (4053351567/10000000000 : ℝ)] ![(38934236440443/100000000000000 : ℝ), (3053233209339/10000000000000 : ℝ), (30533431461099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4877113997/10000000000 : ℝ)|^67 ≤ (38934236440443/100000000000000 : ℝ)^51
        have hw : |(-4877113997/10000000000 : ℝ)|=(4877113997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013310119/2500000000 : ℝ)|^67 ≤ (3053233209339/10000000000000 : ℝ)^51
        have hw : |(1013310119/2500000000 : ℝ)|=(1013310119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4053351567/10000000000 : ℝ)|^67 ≤ (30533431461099/100000000000000 : ℝ)^51
        have hw : |(4053351567/10000000000 : ℝ)|=(4053351567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2098891359/5000000000 : ℝ)*x 0 + (-1744333107/5000000000 : ℝ)*x 1 + (5256227643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098891359/5000000000 : ℝ)^67 ≤ (3996333457107/12500000000000 : ℝ)^51 := by
    have hnat : (2098891359 : ℕ)^67*12500000000000^51 ≤ 3996333457107^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098891359 5000000000 3996333457107 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744333107/5000000000 : ℝ)^67 ≤ (12535741438301/50000000000000 : ℝ)^51 := by
    have hnat : (1744333107 : ℕ)^67*50000000000000^51 ≤ 12535741438301^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744333107 5000000000 12535741438301 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256227643/10000000000 : ℝ)^67 ≤ (1342432795417/3125000000000 : ℝ)^51 := by
    have hnat : (5256227643 : ℕ)^67*3125000000000^51 ≤ 1342432795417^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256227643 10000000000 1342432795417 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098891359/5000000000 : ℝ), (-1744333107/5000000000 : ℝ), (5256227643/10000000000 : ℝ)] ![(3996333457107/12500000000000 : ℝ), (12535741438301/50000000000000 : ℝ), (1342432795417/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098891359/5000000000 : ℝ)|^67 ≤ (3996333457107/12500000000000 : ℝ)^51
        have hw : |(2098891359/5000000000 : ℝ)|=(2098891359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1744333107/5000000000 : ℝ)|^67 ≤ (12535741438301/50000000000000 : ℝ)^51
        have hw : |(-1744333107/5000000000 : ℝ)|=(1744333107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256227643/10000000000 : ℝ)|^67 ≤ (1342432795417/3125000000000 : ℝ)^51
        have hw : |(5256227643/10000000000 : ℝ)|=(5256227643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2098848287/5000000000 : ℝ)*x 0 + (1051257359/2000000000 : ℝ)*x 1 + (-3488690237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098848287/5000000000 : ℝ)^67 ≤ (31969805750639/100000000000000 : ℝ)^51 := by
    have hnat : (2098848287 : ℕ)^67*100000000000000^51 ≤ 31969805750639^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098848287 5000000000 31969805750639 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051257359/2000000000 : ℝ)^67 ≤ (42958484554923/100000000000000 : ℝ)^51 := by
    have hnat : (1051257359 : ℕ)^67*100000000000000^51 ≤ 42958484554923^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051257359 2000000000 42958484554923 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3488690237/10000000000 : ℝ)^67 ≤ (25071709681767/100000000000000 : ℝ)^51 := by
    have hnat : (3488690237 : ℕ)^67*100000000000000^51 ≤ 25071709681767^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3488690237 10000000000 25071709681767 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098848287/5000000000 : ℝ), (1051257359/2000000000 : ℝ), (-3488690237/10000000000 : ℝ)] ![(31969805750639/100000000000000 : ℝ), (42958484554923/100000000000000 : ℝ), (25071709681767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098848287/5000000000 : ℝ)|^67 ≤ (31969805750639/100000000000000 : ℝ)^51
        have hw : |(2098848287/5000000000 : ℝ)|=(2098848287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051257359/2000000000 : ℝ)|^67 ≤ (42958484554923/100000000000000 : ℝ)^51
        have hw : |(1051257359/2000000000 : ℝ)|=(1051257359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3488690237/10000000000 : ℝ)|^67 ≤ (25071709681767/100000000000000 : ℝ)^51
        have hw : |(-3488690237/10000000000 : ℝ)|=(3488690237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302025_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3703542001/10000000000 : ℝ)*x 0 + (927502909/2000000000 : ℝ)*x 1 + (4637367189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3703542001/10000000000 : ℝ)^67 ≤ (1084779597683/4000000000000 : ℝ)^51 := by
    have hnat : (3703542001 : ℕ)^67*4000000000000^51 ≤ 1084779597683^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703542001 10000000000 1084779597683 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (927502909/2000000000 : ℝ)^67 ≤ (36441015598407/100000000000000 : ℝ)^51 := by
    have hnat : (927502909 : ℕ)^67*100000000000000^51 ≤ 36441015598407^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927502909 2000000000 36441015598407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4637367189/10000000000 : ℝ)^67 ≤ (9109873609097/25000000000000 : ℝ)^51 := by
    have hnat : (4637367189 : ℕ)^67*25000000000000^51 ≤ 9109873609097^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637367189 10000000000 9109873609097 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3703542001/10000000000 : ℝ), (927502909/2000000000 : ℝ), (4637367189/10000000000 : ℝ)] ![(1084779597683/4000000000000 : ℝ), (36441015598407/100000000000000 : ℝ), (9109873609097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3703542001/10000000000 : ℝ)|^67 ≤ (1084779597683/4000000000000 : ℝ)^51
        have hw : |(3703542001/10000000000 : ℝ)|=(3703542001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(927502909/2000000000 : ℝ)|^67 ≤ (36441015598407/100000000000000 : ℝ)^51
        have hw : |(927502909/2000000000 : ℝ)|=(927502909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4637367189/10000000000 : ℝ)|^67 ≤ (9109873609097/25000000000000 : ℝ)^51
        have hw : |(4637367189/10000000000 : ℝ)|=(4637367189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302025 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1382973737/2500000000 : ℝ)*X 0 0+(1604678473/5000000000 : ℝ)*X 0 1+(4159691273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((589007017/1250000000 : ℝ)*X 1 0+(-85428853/312500000 : ℝ)*X 1 1+(1081484041/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3478981083/10000000000 : ℝ)*X 2 0+(833209177/1250000000 : ℝ)*X 2 1+(-2517017363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1159572157/2000000000 : ℝ)*X 0 0+(500902289/2000000000 : ℝ)*X 0 1+(561099237/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4439751493/10000000000 : ℝ)*X 1 0+(-1917846743/10000000000 : ℝ)*X 1 1+(6270396379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((549424271/2000000000 : ℝ)*X 2 0+(3763282897/5000000000 : ℝ)*X 2 1+(-2095896471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2239032867/10000000000 : ℝ)*X 0 0+(3067252227/5000000000 : ℝ)*X 0 1+(433722067/1000000000 : ℝ)*X 0 2+(2239032867/10000000000 : ℝ)*X 1 0+(3067252227/5000000000 : ℝ)*X 1 1+(433722067/1000000000 : ℝ)*X 1 2+(2239032867/10000000000 : ℝ)*X 2 0+(3067252227/5000000000 : ℝ)*X 2 1+(433722067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2885852859/5000000000 : ℝ)*X 0 0+(2268903321/10000000000 : ℝ)*X 0 1+(94173603/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1387635039/2500000000 : ℝ)*X 1 0+(-1491653027/5000000000 : ℝ)*X 1 1+(2172033203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3148416923/10000000000 : ℝ)*X 2 0+(3519516019/5000000000 : ℝ)*X 2 1+(-2364691131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((226578487/2000000000 : ℝ)*X 0 0+(3944863493/10000000000 : ℝ)*X 0 1+(7188649279/10000000000 : ℝ)*X 0 2+(226578487/2000000000 : ℝ)*X 1 0+(3944863493/10000000000 : ℝ)*X 1 1+(7188649279/10000000000 : ℝ)*X 1 2+(226578487/2000000000 : ℝ)*X 2 0+(3944863493/10000000000 : ℝ)*X 2 1+(7188649279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-6325956599/10000000000 : ℝ)*X 0 0+(2418452091/10000000000 : ℝ)*X 0 1+(992538253/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((393348263/1000000000 : ℝ)*X 1 0+(-1851635599/5000000000 : ℝ)*X 1 1+(1061893583/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4163789321/10000000000 : ℝ)*X 2 0+(3090373001/5000000000 : ℝ)*X 2 1+(-1193042449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_26 : ((4792847/39062500 : ℝ)*X 0 0+(5433281999/10000000000 : ℝ)*X 0 1+(1158002277/2000000000 : ℝ)*X 0 2+(4792847/39062500 : ℝ)*X 1 0+(5433281999/10000000000 : ℝ)*X 1 1+(1158002277/2000000000 : ℝ)*X 1 2+(4792847/39062500 : ℝ)*X 2 0+(5433281999/10000000000 : ℝ)*X 2 1+(1158002277/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s0_26 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1707/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1707/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34554998869591903455771/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (524196681143/500000000000 : ℝ)*(base50) + (633307142083/1000000000000 : ℝ)*(base59) + (52352231763/1000000000000 : ℝ)*(base60) + (4425747291749/1000000000000 : ℝ)*(major_s0_0) + (4425747291749/1000000000000 : ℝ)*(major_s0_1) + (4425747291749/1000000000000 : ℝ)*(major_s0_2) + (278105821/1000000000000 : ℝ)*(sp_s0_0) + (9410791/1000000000000 : ℝ)*(sp_s0_1) + (588373760329/100000000000 : ℝ)*(sp_s0_7) + (5884565440511/1000000000000 : ℝ)*(sp_s0_8) + (2942287425651/500000000000 : ℝ)*(sp_s0_9) + (2966889827709/1000000000000 : ℝ)*(sp_s0_12) + (559142191/1000000000000 : ℝ)*(sp_s0_13) + (25297147/1000000000000 : ℝ)*(sp_s0_26) + (2966915124857/1000000000000 : ℝ)*(f.failure) + (2942287425651/500000000000 : ℝ)*(f.sum) + (3423901002139073/5000000000000000000000000000 : ℝ)*base63 + (4110653992109587/10000000000000000000000000000 : ℝ)*base65 + (7673429993890413/10000000000000000000000000000 : ℝ)*base67 + (2296375951639073/10000000000000000000000000000 : ℝ)*base69 + (2082296685235257/5000000000000000000000000000 : ℝ)*base71 + (3755614792890413/10000000000000000000000000000 : ℝ)*base73 + (5013718240639073/10000000000000000000000000000 : ℝ)*base75 + (4142857015360927/10000000000000000000000000000 : ℝ)*base77 + (4149916050390413/5000000000000000000000000000 : ℝ)*base79 + (1869/10000000000000000 : ℝ)*base87 + (1869/10000000000000000 : ℝ)*base89 + (1869/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8359/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(8359/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7214083250426862703179/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21451702653/100000000000 : ℝ)*(base40) + (13616344697/250000000000 : ℝ)*(base50) + (427123718299/500000000000 : ℝ)*(base59) + (1654963/1000000000000 : ℝ)*(base60) + (3301489880759/1000000000000 : ℝ)*(major_s0_0) + (3301489880759/1000000000000 : ℝ)*(major_s0_1) + (3301489880759/1000000000000 : ℝ)*(major_s0_2) + (104936189/1000000000000 : ℝ)*(sp_s0_2) + (8341427/500000000000 : ℝ)*(sp_s0_8) + (4389723949347/1000000000000 : ℝ)*(sp_s0_13) + (68589387911/15625000000 : ℝ)*(sp_s0_14) + (4389632572969/1000000000000 : ℝ)*(sp_s0_15) + (2213239847663/1000000000000 : ℝ)*(sp_s0_19) + (13559811/1000000000000 : ℝ)*(sp_s0_20) + (2213239847663/1000000000000 : ℝ)*(f.failure) + (2194868754579/500000000000 : ℝ)*(f.sum) + (525973106648843/5000000000000000000000000000 : ℝ)*base63 + (733732909176783/10000000000000000000000000000 : ℝ)*base64 + (1170122103176783/10000000000000000000000000000 : ℝ)*base67 + (1013110509351157/10000000000000000000000000000 : ℝ)*base68 + (1884365562412813/5000000000000000000000000000 : ℝ)*base70 + (2397755795176783/10000000000000000000000000000 : ℝ)*base73 + (708886862648843/10000000000000000000000000000 : ℝ)*base75 + (3966582646648843/10000000000000000000000000000 : ℝ)*base76 + (2938021146676783/5000000000000000000000000000 : ℝ)*base79 + (1029/10000000000000000 : ℝ)*base86 + (1029/10000000000000000 : ℝ)*base88 + (1029/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2911/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2911/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2933324930923630247583/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5293/50000000000 : ℝ)*(base1) + (2003893/1000000000000 : ℝ)*(base40) + (426637748017/500000000000 : ℝ)*(base50) + (11363113367/12500000000 : ℝ)*(base59) + (2395782585123/500000000000 : ℝ)*(major_s0_0) + (2395782585123/500000000000 : ℝ)*(major_s0_1) + (2395782585123/500000000000 : ℝ)*(major_s0_2) + (1424297/125000000000 : ℝ)*(sp_s0_9) + (3829557/200000000000 : ℝ)*(sp_s0_12) + (342093/31250000000 : ℝ)*(sp_s0_14) + (6370978201311/1000000000000 : ℝ)*(sp_s0_20) + (254838685939/40000000000 : ℝ)*(sp_s0_21) + (254838668043/40000000000 : ℝ)*(sp_s0_22) + (3212131426951/1000000000000 : ℝ)*(sp_s0_26) + (3212150680597/1000000000000 : ℝ)*(f.failure) + (6370978095451/1000000000000 : ℝ)*(f.sum) + (362697226496729/2500000000000000000000000000 : ℝ)*base62 + (1005833611296549/5000000000000000000000000000 : ℝ)*base65 + (940700110203451/5000000000000000000000000000 : ℝ)*base67 + (66311508496729/5000000000000000000000000000 : ℝ)*base68 + (1539199740396639/2500000000000000000000000000 : ℝ)*base71 + (2326084464296549/5000000000000000000000000000 : ℝ)*base72 + (232457467003271/5000000000000000000000000000 : ℝ)*base75 + (2103954275496729/5000000000000000000000000000 : ℝ)*base77 + (990284141046549/2500000000000000000000000000 : ℝ)*base78 + (5449/10000000000000000 : ℝ)*base87 + (5449/10000000000000000 : ℝ)*base89 + (5449/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (1707/6250 : ℝ) ^ (65/16 : ℝ) ≤ (64135151073284297/12500000000000000000 : ℝ) := by
    have hpowers : (1707/6250 : ℝ)^65 ≤ (64135151073284297/12500000000000000000 : ℝ)^16 := by
      have hnat : (1707 : ℕ)^65*12500000000000000000^16 ≤ 64135151073284297^16*6250^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1707 6250 64135151073284297 12500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1707/6250 : ℝ)) (X := (64135151073284297/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12564135151073284297/12500000000000000000 : ℝ) ≤ (10012605339462771/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (12564135151073284297/12500000000000000000 : ℝ)^16 ≤ (10012605339462771/10000000000000000 : ℝ)^65 := by
      have hnat : (12564135151073284297 : ℕ)^16*10000000000000000^65 ≤ 10012605339462771^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12564135151073284297 12500000000000000000 10012605339462771 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012605339462771/10000000000000000 : ℝ)) (X := (12564135151073284297/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6314135151073284297/6250000000000000000 : ℝ) ≤ (10025162265250851/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (6314135151073284297/6250000000000000000 : ℝ)^16 ≤ (10025162265250851/10000000000000000 : ℝ)^65 := by
      have hnat : (6314135151073284297 : ℕ)^16*10000000000000000^65 ≤ 10025162265250851^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6314135151073284297 6250000000000000000 10025162265250851 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025162265250851/10000000000000000 : ℝ)) (X := (6314135151073284297/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(12605339462771/2731200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(52320524117/11380000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1707/6250 : ℝ)) (alpha := (12605339462771/2731200000000000 : ℝ)) (beta := (52320524117/11380000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1707/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(12605339462771/2731200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(52320524117/11380000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8359/50000 : ℝ) ^ (65/16 : ℝ) ≤ (34926599802573951/50000000000000000000 : ℝ) := by
    have hpowers : (8359/50000 : ℝ)^65 ≤ (34926599802573951/50000000000000000000 : ℝ)^16 := by
      have hnat : (8359 : ℕ)^65*50000000000000000000^16 ≤ 34926599802573951^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8359 50000 34926599802573951 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8359/50000 : ℝ)) (X := (34926599802573951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50034926599802573951/50000000000000000000 : ℝ) ≤ (1000171901083731/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50034926599802573951/50000000000000000000 : ℝ)^16 ≤ (1000171901083731/1000000000000000 : ℝ)^65 := by
      have hnat : (50034926599802573951 : ℕ)^16*1000000000000000^65 ≤ 1000171901083731^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034926599802573951 50000000000000000000 1000171901083731 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000171901083731/1000000000000000 : ℝ)) (X := (50034926599802573951/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25034926599802573951/25000000000000000000 : ℝ) ≤ (10003437117337899/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25034926599802573951/25000000000000000000 : ℝ)^16 ≤ (10003437117337899/10000000000000000 : ℝ)^65 := by
      have hnat : (25034926599802573951 : ℕ)^16*10000000000000000^65 ≤ 10003437117337899^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034926599802573951 25000000000000000000 10003437117337899 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003437117337899/10000000000000000 : ℝ)) (X := (25034926599802573951/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(13223160287/12860000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1718106500589/1671800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (8359/50000 : ℝ)) (alpha := (13223160287/12860000000000 : ℝ)) (beta := (1718106500589/1671800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (8359/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(13223160287/12860000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1718106500589/1671800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2911/20000 : ℝ) ^ (65/16 : ℝ) ≤ (19893312574083107/50000000000000000000 : ℝ) := by
    have hpowers : (2911/20000 : ℝ)^65 ≤ (19893312574083107/50000000000000000000 : ℝ)^16 := by
      have hnat : (2911 : ℕ)^65*50000000000000000000^16 ≤ 19893312574083107^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2911 20000 19893312574083107 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2911/20000 : ℝ)) (X := (19893312574083107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50019893312574083107/50000000000000000000 : ℝ) ≤ (10000979216244567/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50019893312574083107/50000000000000000000 : ℝ)^16 ≤ (10000979216244567/10000000000000000 : ℝ)^65 := by
      have hnat : (50019893312574083107 : ℕ)^16*10000000000000000^65 ≤ 10000979216244567^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019893312574083107 50000000000000000000 10000979216244567 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000979216244567/10000000000000000 : ℝ)) (X := (50019893312574083107/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25019893312574083107/25000000000000000000 : ℝ) ≤ (10001958138953659/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25019893312574083107/25000000000000000000 : ℝ)^16 ≤ (10001958138953659/10000000000000000 : ℝ)^65 := by
      have hnat : (25019893312574083107 : ℕ)^16*10000000000000000^65 ≤ 10001958138953659^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019893312574083107 25000000000000000000 10001958138953659 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001958138953659/10000000000000000 : ℝ)) (X := (25019893312574083107/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(979216244567/1455500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(244730677273/363875000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (2911/20000 : ℝ)) (alpha := (979216244567/1455500000000000 : ℝ)) (beta := (244730677273/363875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (2911/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(979216244567/1455500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(244730677273/363875000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4877113997/10000000000 : ℝ)*X 0 0+(1013310119/2500000000 : ℝ)*X 0 1+(4053351567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2098891359/5000000000 : ℝ)*X 1 0+(-1744333107/5000000000 : ℝ)*X 1 1+(5256227643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2098848287/5000000000 : ℝ)*X 2 0+(1051257359/2000000000 : ℝ)*X 2 1+(-3488690237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3703542001/10000000000 : ℝ)*X 0 0+(927502909/2000000000 : ℝ)*X 0 1+(4637367189/10000000000 : ℝ)*X 0 2+(3703542001/10000000000 : ℝ)*X 1 0+(927502909/2000000000 : ℝ)*X 1 1+(4637367189/10000000000 : ℝ)*X 1 2+(3703542001/10000000000 : ℝ)*X 2 0+(927502909/2000000000 : ℝ)*X 2 1+(4637367189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302025_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-35929325505061220872573838502777/6083262250000000000000000000000 : ℝ) := by norm_num
    linear_combination (24523/1000000000000 : ℝ)*(base11) + (39293/1000000000000 : ℝ)*(base13) + (10191/62500000000 : ℝ)*(base43) + (15474435901/250000000000 : ℝ)*(base49) + (293389200189/1000000000000 : ℝ)*(base50) + (17299/500000000000 : ℝ)*(base53) + (261432315897/500000000000 : ℝ)*(base59) + (36737805111/125000000000 : ℝ)*(base60) + (14917/10000 : ℝ)*(major_s1_0) + (93231239809/62500000000 : ℝ)*(major_s1_1) + (745849982701/500000000000 : ℝ)*(major_s1_2) + (1968752907933/1000000000000 : ℝ)*(sp_s1_0) + (393750626961/200000000000 : ℝ)*(sp_s1_1) + (1968753006347/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1968753169403/1000000000000 : ℝ)*(f.sum) + (11218721847265361/116985812500000000000000000000 : ℝ)*base63 + (24977946915351/90968750000000000000000000 : ℝ)*base65 + (245940250135259/417950000000000000000000000 : ℝ)*base67 + (267956542007717/727750000000000000000000000 : ℝ)*base68 + (374949010370942953/621134625000000000000000000000 : ℝ)*base71 + (474011983187/1138000000000000000000000 : ℝ)*base72 + (771238049541/3215000000000000000000000 : ℝ)*base75 + (861904202111/3414000000000000000000000 : ℝ)*base76 + (234859058563626121/237813550000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b012 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=25 := by omega
  rcases hc with rfl
  · exact collision_c302025 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 25 ≤ c.val) (hhi : c.val < 26)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b012 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
