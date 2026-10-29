-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b039
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:45:37.183833+00:00
-- url     : https://prove2.me/submissions/b0d6a8a6-ea2e-4638-b347-68186f1b6c8c

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
theorem collision_support_c322070_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161225423/10000000000 : ℝ)*x 0 + (-3902332057/10000000000 : ℝ)*x 1 + (-6066507161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161225423/10000000000 : ℝ)^83 ≤ (7495359644811/50000000000000 : ℝ)^67 := by
    have hnat : (2161225423 : ℕ)^83*50000000000000^67 ≤ 7495359644811^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161225423 10000000000 7495359644811 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3902332057/10000000000 : ℝ)^83 ≤ (31169512213589/100000000000000 : ℝ)^67 := by
    have hnat : (3902332057 : ℕ)^83*100000000000000^67 ≤ 31169512213589^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3902332057 10000000000 31169512213589 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6066507161/10000000000 : ℝ)^83 ≤ (53839768486909/100000000000000 : ℝ)^67 := by
    have hnat : (6066507161 : ℕ)^83*100000000000000^67 ≤ 53839768486909^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6066507161 10000000000 53839768486909 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161225423/10000000000 : ℝ), (-3902332057/10000000000 : ℝ), (-6066507161/10000000000 : ℝ)] ![(7495359644811/50000000000000 : ℝ), (31169512213589/100000000000000 : ℝ), (53839768486909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161225423/10000000000 : ℝ)|^83 ≤ (7495359644811/50000000000000 : ℝ)^67
        have hw : |(-2161225423/10000000000 : ℝ)|=(2161225423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3902332057/10000000000 : ℝ)|^83 ≤ (31169512213589/100000000000000 : ℝ)^67
        have hw : |(-3902332057/10000000000 : ℝ)|=(3902332057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6066507161/10000000000 : ℝ)|^83 ≤ (53839768486909/100000000000000 : ℝ)^67
        have hw : |(-6066507161/10000000000 : ℝ)|=(6066507161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322070_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6066507127/10000000000 : ℝ)*x 0 + (487791483/1250000000 : ℝ)*x 1 + (-270153211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6066507127/10000000000 : ℝ)^83 ≤ (53839768113103/100000000000000 : ℝ)^67 := by
    have hnat : (6066507127 : ℕ)^83*100000000000000^67 ≤ 53839768113103^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6066507127 10000000000 53839768113103 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487791483/1250000000 : ℝ)^83 ≤ (7792377575971/25000000000000 : ℝ)^67 := by
    have hnat : (487791483 : ℕ)^83*25000000000000^67 ≤ 7792377575971^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487791483 1250000000 7792377575971 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270153211/1250000000 : ℝ)^83 ≤ (14990721566667/100000000000000 : ℝ)^67 := by
    have hnat : (270153211 : ℕ)^83*100000000000000^67 ≤ 14990721566667^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270153211 1250000000 14990721566667 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6066507127/10000000000 : ℝ), (487791483/1250000000 : ℝ), (-270153211/1250000000 : ℝ)] ![(53839768113103/100000000000000 : ℝ), (7792377575971/25000000000000 : ℝ), (14990721566667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6066507127/10000000000 : ℝ)|^83 ≤ (53839768113103/100000000000000 : ℝ)^67
        have hw : |(6066507127/10000000000 : ℝ)|=(6066507127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487791483/1250000000 : ℝ)|^83 ≤ (7792377575971/25000000000000 : ℝ)^67
        have hw : |(487791483/1250000000 : ℝ)|=(487791483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270153211/1250000000 : ℝ)|^83 ≤ (14990721566667/100000000000000 : ℝ)^67
        have hw : |(-270153211/1250000000 : ℝ)|=(270153211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322070_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2293027/6250000 : ℝ)*x 0 + (-1247041427/2500000000 : ℝ)*x 1 + (3668843831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2293027/6250000 : ℝ)^83 ≤ (28875938795771/100000000000000 : ℝ)^67 := by
    have hnat : (2293027 : ℕ)^83*100000000000000^67 ≤ 28875938795771^67*6250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293027 6250000 28875938795771 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247041427/2500000000 : ℝ)^83 ≤ (42248116241529/100000000000000 : ℝ)^67 := by
    have hnat : (1247041427 : ℕ)^83*100000000000000^67 ≤ 42248116241529^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247041427 2500000000 42248116241529 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3668843831/10000000000 : ℝ)^83 ≤ (28875944948101/100000000000000 : ℝ)^67 := by
    have hnat : (3668843831 : ℕ)^83*100000000000000^67 ≤ 28875944948101^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668843831 10000000000 28875944948101 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2293027/6250000 : ℝ), (-1247041427/2500000000 : ℝ), (3668843831/10000000000 : ℝ)] ![(28875938795771/100000000000000 : ℝ), (42248116241529/100000000000000 : ℝ), (28875944948101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2293027/6250000 : ℝ)|^83 ≤ (28875938795771/100000000000000 : ℝ)^67
        have hw : |(2293027/6250000 : ℝ)|=(2293027/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1247041427/2500000000 : ℝ)|^83 ≤ (42248116241529/100000000000000 : ℝ)^67
        have hw : |(-1247041427/2500000000 : ℝ)|=(1247041427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3668843831/10000000000 : ℝ)|^83 ≤ (28875944948101/100000000000000 : ℝ)^67
        have hw : |(3668843831/10000000000 : ℝ)|=(3668843831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322070_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (492047911/1000000000 : ℝ)*x 0 + (-2383309519/10000000000 : ℝ)*x 1 + (-4920478893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492047911/1000000000 : ℝ)^83 ≤ (10384771081747/25000000000000 : ℝ)^67 := by
    have hnat : (492047911 : ℕ)^83*25000000000000^67 ≤ 10384771081747^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492047911 1000000000 10384771081747 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2383309519/10000000000 : ℝ)^83 ≤ (8460916800203/50000000000000 : ℝ)^67 := by
    have hnat : (2383309519 : ℕ)^83*50000000000000^67 ≤ 8460916800203^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383309519 10000000000 8460916800203 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4920478893/10000000000 : ℝ)^83 ≤ (2076954102879/5000000000000 : ℝ)^67 := by
    have hnat : (4920478893 : ℕ)^83*5000000000000^67 ≤ 2076954102879^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4920478893 10000000000 2076954102879 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(492047911/1000000000 : ℝ), (-2383309519/10000000000 : ℝ), (-4920478893/10000000000 : ℝ)] ![(10384771081747/25000000000000 : ℝ), (8460916800203/50000000000000 : ℝ), (2076954102879/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(492047911/1000000000 : ℝ)|^83 ≤ (10384771081747/25000000000000 : ℝ)^67
        have hw : |(492047911/1000000000 : ℝ)|=(492047911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2383309519/10000000000 : ℝ)|^83 ≤ (8460916800203/50000000000000 : ℝ)^67
        have hw : |(-2383309519/10000000000 : ℝ)|=(2383309519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4920478893/10000000000 : ℝ)|^83 ≤ (2076954102879/5000000000000 : ℝ)^67
        have hw : |(-4920478893/10000000000 : ℝ)|=(4920478893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322070 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2161225423/10000000000 : ℝ)*X 0 0+(-3902332057/10000000000 : ℝ)*X 0 1+(-6066507161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6066507127/10000000000 : ℝ)*X 1 0+(487791483/1250000000 : ℝ)*X 1 1+(-270153211/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2293027/6250000 : ℝ)*X 2 0+(-1247041427/2500000000 : ℝ)*X 2 1+(3668843831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((492047911/1000000000 : ℝ)*X 0 0+(-2383309519/10000000000 : ℝ)*X 0 1+(-4920478893/10000000000 : ℝ)*X 0 2+(492047911/1000000000 : ℝ)*X 1 0+(-2383309519/10000000000 : ℝ)*X 1 1+(-4920478893/10000000000 : ℝ)*X 1 2+(492047911/1000000000 : ℝ)*X 2 0+(-2383309519/10000000000 : ℝ)*X 2 1+(-4920478893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-8492575085593160926587982863/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13789/40000000000 : ℝ)*(base3) + (27097/500000000000 : ℝ)*(base21) + (322071610137/500000000000 : ℝ)*(base39) + (119419/1000000000000 : ℝ)*(base40) + (135077/1000000000000 : ℝ)*(base43) + (54339504401/250000000000 : ℝ)*(base49) + (5062220927/12500000000 : ℝ)*(base59) + (56717/200000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s0_0) + (1929899864923/1000000000000 : ℝ)*(major_s0_1) + (19299/10000 : ℝ)*(major_s0_2) + (2830858226779/1000000000000 : ℝ)*(sp_s0_0) + (2830858706581/1000000000000 : ℝ)*(sp_s0_1) + (566171634517/200000000000 : ℝ)*(sp_s0_2) + (39999986211/40000000000 : ℝ)*(sp_s0_6) + (566171672371/200000000000 : ℝ)*(f.sum) + (1331731131427621/2000000000000000000000000000 : ℝ)*base62 + (3481175907/2500000000000000000000 : ℝ)*base65 + (1183474649470659/2500000000000000000000000000 : ℝ)*base67 + (7966494837/10000000000000000000000 : ℝ)*base68 + (12704965441/10000000000000000000000 : ℝ)*base71 + (2343450197/10000000000000000000000 : ℝ)*base72 + (1309428674827621/2000000000000000000000000000 : ℝ)*base74 + (1435878221/2000000000000000000000 : ℝ)*base77 + (452763114029341/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c322071_s0_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3550857561/10000000000 : ℝ)*x 0 + (506798909/1000000000 : ℝ)*x 1 + (3700277809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3550857561/10000000000 : ℝ)^83 ≤ (27730017727969/100000000000000 : ℝ)^67 := by
    have hnat : (3550857561 : ℕ)^83*100000000000000^67 ≤ 27730017727969^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3550857561 10000000000 27730017727969 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506798909/1000000000 : ℝ)^83 ≤ (43087239171641/100000000000000 : ℝ)^67 := by
    have hnat : (506798909 : ℕ)^83*100000000000000^67 ≤ 43087239171641^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506798909 1000000000 43087239171641 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3700277809/10000000000 : ℝ)^83 ≤ (29182743085507/100000000000000 : ℝ)^67 := by
    have hnat : (3700277809 : ℕ)^83*100000000000000^67 ≤ 29182743085507^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3700277809 10000000000 29182743085507 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3550857561/10000000000 : ℝ), (506798909/1000000000 : ℝ), (3700277809/10000000000 : ℝ)] ![(27730017727969/100000000000000 : ℝ), (43087239171641/100000000000000 : ℝ), (29182743085507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3550857561/10000000000 : ℝ)|^83 ≤ (27730017727969/100000000000000 : ℝ)^67
        have hw : |(3550857561/10000000000 : ℝ)|=(3550857561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506798909/1000000000 : ℝ)|^83 ≤ (43087239171641/100000000000000 : ℝ)^67
        have hw : |(506798909/1000000000 : ℝ)|=(506798909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3700277809/10000000000 : ℝ)|^83 ≤ (29182743085507/100000000000000 : ℝ)^67
        have hw : |(3700277809/10000000000 : ℝ)|=(3700277809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3141542487/5000000000 : ℝ)*x 0 + (-3596266909/10000000000 : ℝ)*x 1 + (-2231750767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3141542487/5000000000 : ℝ)^83 ≤ (702886881441/1250000000000 : ℝ)^67 := by
    have hnat : (3141542487 : ℕ)^83*1250000000000^67 ≤ 702886881441^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3141542487 5000000000 702886881441 1250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3596266909/10000000000 : ℝ)^83 ≤ (28169990660389/100000000000000 : ℝ)^67 := by
    have hnat : (3596266909 : ℕ)^83*100000000000000^67 ≤ 28169990660389^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3596266909 10000000000 28169990660389 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231750767/10000000000 : ℝ)^83 ≤ (7799529405521/50000000000000 : ℝ)^67 := by
    have hnat : (2231750767 : ℕ)^83*50000000000000^67 ≤ 7799529405521^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231750767 10000000000 7799529405521 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3141542487/5000000000 : ℝ), (-3596266909/10000000000 : ℝ), (-2231750767/10000000000 : ℝ)] ![(702886881441/1250000000000 : ℝ), (28169990660389/100000000000000 : ℝ), (7799529405521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3141542487/5000000000 : ℝ)|^83 ≤ (702886881441/1250000000000 : ℝ)^67
        have hw : |(3141542487/5000000000 : ℝ)|=(3141542487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3596266909/10000000000 : ℝ)|^83 ≤ (28169990660389/100000000000000 : ℝ)^67
        have hw : |(-3596266909/10000000000 : ℝ)|=(3596266909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231750767/10000000000 : ℝ)|^83 ≤ (7799529405521/50000000000000 : ℝ)^67
        have hw : |(-2231750767/10000000000 : ℝ)|=(2231750767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-94323613/250000000 : ℝ)*x 0 + (-4838523883/10000000000 : ℝ)*x 1 + (5959587/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94323613/250000000 : ℝ)^83 ≤ (29894354197859/100000000000000 : ℝ)^67 := by
    have hnat : (94323613 : ℕ)^83*100000000000000^67 ≤ 29894354197859^67*250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94323613 250000000 29894354197859 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4838523883/10000000000 : ℝ)^83 ≤ (40683700139671/100000000000000 : ℝ)^67 := by
    have hnat : (4838523883 : ℕ)^83*100000000000000^67 ≤ 40683700139671^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838523883 10000000000 40683700139671 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5959587/16000000 : ℝ)^83 ≤ (29421945656687/100000000000000 : ℝ)^67 := by
    have hnat : (5959587 : ℕ)^83*100000000000000^67 ≤ 29421945656687^67*16000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959587 16000000 29421945656687 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94323613/250000000 : ℝ), (-4838523883/10000000000 : ℝ), (5959587/16000000 : ℝ)] ![(29894354197859/100000000000000 : ℝ), (40683700139671/100000000000000 : ℝ), (29421945656687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94323613/250000000 : ℝ)|^83 ≤ (29894354197859/100000000000000 : ℝ)^67
        have hw : |(-94323613/250000000 : ℝ)|=(94323613/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4838523883/10000000000 : ℝ)|^83 ≤ (40683700139671/100000000000000 : ℝ)^67
        have hw : |(-4838523883/10000000000 : ℝ)|=(4838523883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5959587/16000000 : ℝ)|^83 ≤ (29421945656687/100000000000000 : ℝ)^67
        have hw : |(5959587/16000000 : ℝ)|=(5959587/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (132522463/400000000 : ℝ)*x 0 + (10833467/20000000 : ℝ)*x 1 + (3554147443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132522463/400000000 : ℝ)^83 ≤ (5089644457723/20000000000000 : ℝ)^67 := by
    have hnat : (132522463 : ℕ)^83*20000000000000^67 ≤ 5089644457723^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132522463 400000000 5089644457723 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10833467/20000000 : ℝ)^83 ≤ (23394964548147/50000000000000 : ℝ)^67 := by
    have hnat : (10833467 : ℕ)^83*50000000000000^67 ≤ 23394964548147^67*20000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10833467 20000000 23394964548147 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3554147443/10000000000 : ℝ)^83 ≤ (27761848600069/100000000000000 : ℝ)^67 := by
    have hnat : (3554147443 : ℕ)^83*100000000000000^67 ≤ 27761848600069^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3554147443 10000000000 27761848600069 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132522463/400000000 : ℝ), (10833467/20000000 : ℝ), (3554147443/10000000000 : ℝ)] ![(5089644457723/20000000000000 : ℝ), (23394964548147/50000000000000 : ℝ), (27761848600069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132522463/400000000 : ℝ)|^83 ≤ (5089644457723/20000000000000 : ℝ)^67
        have hw : |(132522463/400000000 : ℝ)|=(132522463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10833467/20000000 : ℝ)|^83 ≤ (23394964548147/50000000000000 : ℝ)^67
        have hw : |(10833467/20000000 : ℝ)|=(10833467/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3554147443/10000000000 : ℝ)|^83 ≤ (27761848600069/100000000000000 : ℝ)^67
        have hw : |(3554147443/10000000000 : ℝ)|=(3554147443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6057969913/10000000000 : ℝ)*x 0 + (-1793703583/5000000000 : ℝ)*x 1 + (-39441239/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6057969913/10000000000 : ℝ)^83 ≤ (53745923160683/100000000000000 : ℝ)^67 := by
    have hnat : (6057969913 : ℕ)^83*100000000000000^67 ≤ 53745923160683^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6057969913 10000000000 53745923160683 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793703583/5000000000 : ℝ)^83 ≤ (28084043536339/100000000000000 : ℝ)^67 := by
    have hnat : (1793703583 : ℕ)^83*100000000000000^67 ≤ 28084043536339^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793703583 5000000000 28084043536339 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39441239/156250000 : ℝ)^83 ≤ (1135627080411/6250000000000 : ℝ)^67 := by
    have hnat : (39441239 : ℕ)^83*6250000000000^67 ≤ 1135627080411^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39441239 156250000 1135627080411 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6057969913/10000000000 : ℝ), (-1793703583/5000000000 : ℝ), (-39441239/156250000 : ℝ)] ![(53745923160683/100000000000000 : ℝ), (28084043536339/100000000000000 : ℝ), (1135627080411/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6057969913/10000000000 : ℝ)|^83 ≤ (53745923160683/100000000000000 : ℝ)^67
        have hw : |(6057969913/10000000000 : ℝ)|=(6057969913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793703583/5000000000 : ℝ)|^83 ≤ (28084043536339/100000000000000 : ℝ)^67
        have hw : |(-1793703583/5000000000 : ℝ)|=(1793703583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39441239/156250000 : ℝ)|^83 ≤ (1135627080411/6250000000000 : ℝ)^67
        have hw : |(-39441239/156250000 : ℝ)|=(39441239/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913243/5000000000 : ℝ)*x 0 + (-1387064201/10000000000 : ℝ)*x 1 + (9294894669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913243/5000000000 : ℝ)^83 ≤ (5844567763/100000000000000 : ℝ)^67 := by
    have hnat : (1913243 : ℕ)^83*100000000000000^67 ≤ 5844567763^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913243 5000000000 5844567763 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387064201/10000000000 : ℝ)^83 ≤ (1730828733077/20000000000000 : ℝ)^67 := by
    have hnat : (1387064201 : ℕ)^83*20000000000000^67 ≤ 1730828733077^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387064201 10000000000 1730828733077 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9294894669/10000000000 : ℝ)^83 ≤ (91340011749481/100000000000000 : ℝ)^67 := by
    have hnat : (9294894669 : ℕ)^83*100000000000000^67 ≤ 91340011749481^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9294894669 10000000000 91340011749481 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913243/5000000000 : ℝ), (-1387064201/10000000000 : ℝ), (9294894669/10000000000 : ℝ)] ![(5844567763/100000000000000 : ℝ), (1730828733077/20000000000000 : ℝ), (91340011749481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913243/5000000000 : ℝ)|^83 ≤ (5844567763/100000000000000 : ℝ)^67
        have hw : |(-1913243/5000000000 : ℝ)|=(1913243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387064201/10000000000 : ℝ)|^83 ≤ (1730828733077/20000000000000 : ℝ)^67
        have hw : |(-1387064201/10000000000 : ℝ)|=(1387064201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9294894669/10000000000 : ℝ)|^83 ≤ (91340011749481/100000000000000 : ℝ)^67
        have hw : |(9294894669/10000000000 : ℝ)|=(9294894669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3246817667/10000000000 : ℝ)*x 0 + (-3082153459/10000000000 : ℝ)*x 1 + (2945228291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3246817667/10000000000 : ℝ)^83 ≤ (24819391543023/100000000000000 : ℝ)^67 := by
    have hnat : (3246817667 : ℕ)^83*100000000000000^67 ≤ 24819391543023^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3246817667 10000000000 24819391543023 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3082153459/10000000000 : ℝ)^83 ≤ (23269636733753/100000000000000 : ℝ)^67 := by
    have hnat : (3082153459 : ℕ)^83*100000000000000^67 ≤ 23269636733753^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3082153459 10000000000 23269636733753 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2945228291/5000000000 : ℝ)^83 ≤ (6488871463563/12500000000000 : ℝ)^67 := by
    have hnat : (2945228291 : ℕ)^83*12500000000000^67 ≤ 6488871463563^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2945228291 5000000000 6488871463563 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3246817667/10000000000 : ℝ), (-3082153459/10000000000 : ℝ), (2945228291/5000000000 : ℝ)] ![(24819391543023/100000000000000 : ℝ), (23269636733753/100000000000000 : ℝ), (6488871463563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3246817667/10000000000 : ℝ)|^83 ≤ (24819391543023/100000000000000 : ℝ)^67
        have hw : |(-3246817667/10000000000 : ℝ)|=(3246817667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3082153459/10000000000 : ℝ)|^83 ≤ (23269636733753/100000000000000 : ℝ)^67
        have hw : |(-3082153459/10000000000 : ℝ)|=(3082153459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2945228291/5000000000 : ℝ)|^83 ≤ (6488871463563/12500000000000 : ℝ)^67
        have hw : |(2945228291/5000000000 : ℝ)|=(2945228291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5111414987/10000000000 : ℝ)*x 0 + (4585503023/10000000000 : ℝ)*x 1 + (1274443203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5111414987/10000000000 : ℝ)^83 ≤ (21772536686433/50000000000000 : ℝ)^67 := by
    have hnat : (5111414987 : ℕ)^83*50000000000000^67 ≤ 21772536686433^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111414987 10000000000 21772536686433 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4585503023/10000000000 : ℝ)^83 ≤ (38064854521641/100000000000000 : ℝ)^67 := by
    have hnat : (4585503023 : ℕ)^83*100000000000000^67 ≤ 38064854521641^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585503023 10000000000 38064854521641 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274443203/5000000000 : ℝ)^83 ≤ (18390072093563/100000000000000 : ℝ)^67 := by
    have hnat : (1274443203 : ℕ)^83*100000000000000^67 ≤ 18390072093563^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274443203 5000000000 18390072093563 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5111414987/10000000000 : ℝ), (4585503023/10000000000 : ℝ), (1274443203/5000000000 : ℝ)] ![(21772536686433/50000000000000 : ℝ), (38064854521641/100000000000000 : ℝ), (18390072093563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5111414987/10000000000 : ℝ)|^83 ≤ (21772536686433/50000000000000 : ℝ)^67
        have hw : |(5111414987/10000000000 : ℝ)|=(5111414987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4585503023/10000000000 : ℝ)|^83 ≤ (38064854521641/100000000000000 : ℝ)^67
        have hw : |(4585503023/10000000000 : ℝ)|=(4585503023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274443203/5000000000 : ℝ)|^83 ≤ (18390072093563/100000000000000 : ℝ)^67
        have hw : |(1274443203/5000000000 : ℝ)|=(1274443203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1517335933/2000000000 : ℝ)*x 0 + (-358467969/1250000000 : ℝ)*x 1 + (-1261495813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1517335933/2000000000 : ℝ)^83 ≤ (71024369680213/100000000000000 : ℝ)^67 := by
    have hnat : (1517335933 : ℕ)^83*100000000000000^67 ≤ 71024369680213^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517335933 2000000000 71024369680213 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358467969/1250000000 : ℝ)^83 ≤ (10640639793637/50000000000000 : ℝ)^67 := by
    have hnat : (358467969 : ℕ)^83*50000000000000^67 ≤ 10640639793637^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358467969 1250000000 10640639793637 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1261495813/10000000000 : ℝ)^83 ≤ (961793839071/12500000000000 : ℝ)^67 := by
    have hnat : (1261495813 : ℕ)^83*12500000000000^67 ≤ 961793839071^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261495813 10000000000 961793839071 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1517335933/2000000000 : ℝ), (-358467969/1250000000 : ℝ), (-1261495813/10000000000 : ℝ)] ![(71024369680213/100000000000000 : ℝ), (10640639793637/50000000000000 : ℝ), (961793839071/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1517335933/2000000000 : ℝ)|^83 ≤ (71024369680213/100000000000000 : ℝ)^67
        have hw : |(1517335933/2000000000 : ℝ)|=(1517335933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358467969/1250000000 : ℝ)|^83 ≤ (10640639793637/50000000000000 : ℝ)^67
        have hw : |(-358467969/1250000000 : ℝ)|=(358467969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1261495813/10000000000 : ℝ)|^83 ≤ (961793839071/12500000000000 : ℝ)^67
        have hw : |(-1261495813/10000000000 : ℝ)|=(1261495813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-22413/2500000000 : ℝ)*x 0 + (-218903029/1250000000 : ℝ)*x 1 + (181132277/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22413/2500000000 : ℝ)^83 ≤ (11174579/20000000000000 : ℝ)^67 := by
    have hnat : (22413 : ℕ)^83*20000000000000^67 ≤ 11174579^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22413 2500000000 11174579 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218903029/1250000000 : ℝ)^83 ≤ (2887933982457/25000000000000 : ℝ)^67 := by
    have hnat : (218903029 : ℕ)^83*25000000000000^67 ≤ 2887933982457^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218903029 1250000000 2887933982457 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181132277/200000000 : ℝ)^83 ≤ (44224104094561/50000000000000 : ℝ)^67 := by
    have hnat : (181132277 : ℕ)^83*50000000000000^67 ≤ 44224104094561^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181132277 200000000 44224104094561 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22413/2500000000 : ℝ), (-218903029/1250000000 : ℝ), (181132277/200000000 : ℝ)] ![(11174579/20000000000000 : ℝ), (2887933982457/25000000000000 : ℝ), (44224104094561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22413/2500000000 : ℝ)|^83 ≤ (11174579/20000000000000 : ℝ)^67
        have hw : |(-22413/2500000000 : ℝ)|=(22413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218903029/1250000000 : ℝ)|^83 ≤ (2887933982457/25000000000000 : ℝ)^67
        have hw : |(-218903029/1250000000 : ℝ)|=(218903029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181132277/200000000 : ℝ)|^83 ≤ (44224104094561/50000000000000 : ℝ)^67
        have hw : |(181132277/200000000 : ℝ)|=(181132277/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3317685303/10000000000 : ℝ)*x 0 + (-857411857/2000000000 : ℝ)*x 1 + (59042181/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3317685303/10000000000 : ℝ)^83 ≤ (25492226662769/100000000000000 : ℝ)^67 := by
    have hnat : (3317685303 : ℕ)^83*100000000000000^67 ≤ 25492226662769^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3317685303 10000000000 25492226662769 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857411857/2000000000 : ℝ)^83 ≤ (875501688487/2500000000000 : ℝ)^67 := by
    have hnat : (857411857 : ℕ)^83*2500000000000^67 ≤ 875501688487^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857411857 2000000000 875501688487 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59042181/125000000 : ℝ)^83 ≤ (39487705777483/100000000000000 : ℝ)^67 := by
    have hnat : (59042181 : ℕ)^83*100000000000000^67 ≤ 39487705777483^67*125000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59042181 125000000 39487705777483 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3317685303/10000000000 : ℝ), (-857411857/2000000000 : ℝ), (59042181/125000000 : ℝ)] ![(25492226662769/100000000000000 : ℝ), (875501688487/2500000000000 : ℝ), (39487705777483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3317685303/10000000000 : ℝ)|^83 ≤ (25492226662769/100000000000000 : ℝ)^67
        have hw : |(-3317685303/10000000000 : ℝ)|=(3317685303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-857411857/2000000000 : ℝ)|^83 ≤ (875501688487/2500000000000 : ℝ)^67
        have hw : |(-857411857/2000000000 : ℝ)|=(857411857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59042181/125000000 : ℝ)|^83 ≤ (39487705777483/100000000000000 : ℝ)^67
        have hw : |(59042181/125000000 : ℝ)|=(59042181/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2953167469/10000000000 : ℝ)*x 0 + (5465298541/10000000000 : ℝ)*x 1 + (480843691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2953167469/10000000000 : ℝ)^83 ≤ (22069358310339/100000000000000 : ℝ)^67 := by
    have hnat : (2953167469 : ℕ)^83*100000000000000^67 ≤ 22069358310339^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953167469 10000000000 22069358310339 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465298541/10000000000 : ℝ)^83 ≤ (47310171316491/100000000000000 : ℝ)^67 := by
    have hnat : (5465298541 : ℕ)^83*100000000000000^67 ≤ 47310171316491^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465298541 10000000000 47310171316491 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480843691/1250000000 : ℝ)^83 ≤ (30620470362199/100000000000000 : ℝ)^67 := by
    have hnat : (480843691 : ℕ)^83*100000000000000^67 ≤ 30620470362199^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480843691 1250000000 30620470362199 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2953167469/10000000000 : ℝ), (5465298541/10000000000 : ℝ), (480843691/1250000000 : ℝ)] ![(22069358310339/100000000000000 : ℝ), (47310171316491/100000000000000 : ℝ), (30620470362199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2953167469/10000000000 : ℝ)|^83 ≤ (22069358310339/100000000000000 : ℝ)^67
        have hw : |(2953167469/10000000000 : ℝ)|=(2953167469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465298541/10000000000 : ℝ)|^83 ≤ (47310171316491/100000000000000 : ℝ)^67
        have hw : |(5465298541/10000000000 : ℝ)|=(5465298541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(480843691/1250000000 : ℝ)|^83 ≤ (30620470362199/100000000000000 : ℝ)^67
        have hw : |(480843691/1250000000 : ℝ)|=(480843691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (354806653/500000000 : ℝ)*x 0 + (-735496199/2500000000 : ℝ)*x 1 + (-942466581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354806653/500000000 : ℝ)^83 ≤ (32689995386241/50000000000000 : ℝ)^67 := by
    have hnat : (354806653 : ℕ)^83*50000000000000^67 ≤ 32689995386241^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354806653 500000000 32689995386241 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735496199/2500000000 : ℝ)^83 ≤ (21965878898877/100000000000000 : ℝ)^67 := by
    have hnat : (735496199 : ℕ)^83*100000000000000^67 ≤ 21965878898877^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735496199 2500000000 21965878898877 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942466581/5000000000 : ℝ)^83 ≤ (6327065157783/50000000000000 : ℝ)^67 := by
    have hnat : (942466581 : ℕ)^83*50000000000000^67 ≤ 6327065157783^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942466581 5000000000 6327065157783 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(354806653/500000000 : ℝ), (-735496199/2500000000 : ℝ), (-942466581/5000000000 : ℝ)] ![(32689995386241/50000000000000 : ℝ), (21965878898877/100000000000000 : ℝ), (6327065157783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(354806653/500000000 : ℝ)|^83 ≤ (32689995386241/50000000000000 : ℝ)^67
        have hw : |(354806653/500000000 : ℝ)|=(354806653/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-735496199/2500000000 : ℝ)|^83 ≤ (21965878898877/100000000000000 : ℝ)^67
        have hw : |(-735496199/2500000000 : ℝ)|=(735496199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-942466581/5000000000 : ℝ)|^83 ≤ (6327065157783/50000000000000 : ℝ)^67
        have hw : |(-942466581/5000000000 : ℝ)|=(942466581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-860006557/2500000000 : ℝ)*x 0 + (-757372747/2000000000 : ℝ)*x 1 + (5088857221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860006557/2500000000 : ℝ)^83 ≤ (533236574029/2000000000000 : ℝ)^67 := by
    have hnat : (860006557 : ℕ)^83*2000000000000^67 ≤ 533236574029^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860006557 2500000000 533236574029 2000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757372747/2000000000 : ℝ)^83 ≤ (7507759564989/25000000000000 : ℝ)^67 := by
    have hnat : (757372747 : ℕ)^83*25000000000000^67 ≤ 7507759564989^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757372747 2000000000 7507759564989 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5088857221/10000000000 : ℝ)^83 ≤ (43307133024821/100000000000000 : ℝ)^67 := by
    have hnat : (5088857221 : ℕ)^83*100000000000000^67 ≤ 43307133024821^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088857221 10000000000 43307133024821 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-860006557/2500000000 : ℝ), (-757372747/2000000000 : ℝ), (5088857221/10000000000 : ℝ)] ![(533236574029/2000000000000 : ℝ), (7507759564989/25000000000000 : ℝ), (43307133024821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-860006557/2500000000 : ℝ)|^83 ≤ (533236574029/2000000000000 : ℝ)^67
        have hw : |(-860006557/2500000000 : ℝ)|=(860006557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-757372747/2000000000 : ℝ)|^83 ≤ (7507759564989/25000000000000 : ℝ)^67
        have hw : |(-757372747/2000000000 : ℝ)|=(757372747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5088857221/10000000000 : ℝ)|^83 ≤ (43307133024821/100000000000000 : ℝ)^67
        have hw : |(5088857221/10000000000 : ℝ)|=(5088857221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2094433249/5000000000 : ℝ)*x 0 + (4622628393/10000000000 : ℝ)*x 1 + (3529532819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094433249/5000000000 : ℝ)^83 ≤ (34029135177449/100000000000000 : ℝ)^67 := by
    have hnat : (2094433249 : ℕ)^83*100000000000000^67 ≤ 34029135177449^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094433249 5000000000 34029135177449 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4622628393/10000000000 : ℝ)^83 ≤ (38447001164483/100000000000000 : ℝ)^67 := by
    have hnat : (4622628393 : ℕ)^83*100000000000000^67 ≤ 38447001164483^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622628393 10000000000 38447001164483 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3529532819/10000000000 : ℝ)^83 ≤ (27523863635487/100000000000000 : ℝ)^67 := by
    have hnat : (3529532819 : ℕ)^83*100000000000000^67 ≤ 27523863635487^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3529532819 10000000000 27523863635487 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094433249/5000000000 : ℝ), (4622628393/10000000000 : ℝ), (3529532819/10000000000 : ℝ)] ![(34029135177449/100000000000000 : ℝ), (38447001164483/100000000000000 : ℝ), (27523863635487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094433249/5000000000 : ℝ)|^83 ≤ (34029135177449/100000000000000 : ℝ)^67
        have hw : |(2094433249/5000000000 : ℝ)|=(2094433249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4622628393/10000000000 : ℝ)|^83 ≤ (38447001164483/100000000000000 : ℝ)^67
        have hw : |(4622628393/10000000000 : ℝ)|=(4622628393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3529532819/10000000000 : ℝ)|^83 ≤ (27523863635487/100000000000000 : ℝ)^67
        have hw : |(3529532819/10000000000 : ℝ)|=(3529532819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5006551521/10000000000 : ℝ)*x 0 + (-1040319461/2500000000 : ℝ)*x 1 + (-3139501087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5006551521/10000000000 : ℝ)^83 ≤ (21220555056997/50000000000000 : ℝ)^67 := by
    have hnat : (5006551521 : ℕ)^83*50000000000000^67 ≤ 21220555056997^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006551521 10000000000 21220555056997 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040319461/2500000000 : ℝ)^83 ≤ (16875854973951/50000000000000 : ℝ)^67 := by
    have hnat : (1040319461 : ℕ)^83*50000000000000^67 ≤ 16875854973951^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040319461 2500000000 16875854973951 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3139501087/10000000000 : ℝ)^83 ≤ (23807179928359/100000000000000 : ℝ)^67 := by
    have hnat : (3139501087 : ℕ)^83*100000000000000^67 ≤ 23807179928359^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139501087 10000000000 23807179928359 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5006551521/10000000000 : ℝ), (-1040319461/2500000000 : ℝ), (-3139501087/10000000000 : ℝ)] ![(21220555056997/50000000000000 : ℝ), (16875854973951/50000000000000 : ℝ), (23807179928359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5006551521/10000000000 : ℝ)|^83 ≤ (21220555056997/50000000000000 : ℝ)^67
        have hw : |(5006551521/10000000000 : ℝ)|=(5006551521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040319461/2500000000 : ℝ)|^83 ≤ (16875854973951/50000000000000 : ℝ)^67
        have hw : |(-1040319461/2500000000 : ℝ)|=(1040319461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3139501087/10000000000 : ℝ)|^83 ≤ (23807179928359/100000000000000 : ℝ)^67
        have hw : |(-3139501087/10000000000 : ℝ)|=(3139501087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322071_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3088681719/10000000000 : ℝ)*x 0 + (-3190785037/10000000000 : ℝ)*x 1 + (296666389/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3088681719/10000000000 : ℝ)^83 ≤ (23330709253729/100000000000000 : ℝ)^67 := by
    have hnat : (3088681719 : ℕ)^83*100000000000000^67 ≤ 23330709253729^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088681719 10000000000 23330709253729 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3190785037/10000000000 : ℝ)^83 ≤ (2428987719789/10000000000000 : ℝ)^67 := by
    have hnat : (3190785037 : ℕ)^83*10000000000000^67 ≤ 2428987719789^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190785037 10000000000 2428987719789 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296666389/500000000 : ℝ)^83 ≤ (10475882706411/20000000000000 : ℝ)^67 := by
    have hnat : (296666389 : ℕ)^83*20000000000000^67 ≤ 10475882706411^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296666389 500000000 10475882706411 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3088681719/10000000000 : ℝ), (-3190785037/10000000000 : ℝ), (296666389/500000000 : ℝ)] ![(23330709253729/100000000000000 : ℝ), (2428987719789/10000000000000 : ℝ), (10475882706411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3088681719/10000000000 : ℝ)|^83 ≤ (23330709253729/100000000000000 : ℝ)^67
        have hw : |(3088681719/10000000000 : ℝ)|=(3088681719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3190785037/10000000000 : ℝ)|^83 ≤ (2428987719789/10000000000000 : ℝ)^67
        have hw : |(-3190785037/10000000000 : ℝ)|=(3190785037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(296666389/500000000 : ℝ)|^83 ≤ (10475882706411/20000000000000 : ℝ)^67
        have hw : |(296666389/500000000 : ℝ)|=(296666389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322071 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (167697/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3550857561/10000000000 : ℝ)*X 1 0+(506798909/1000000000 : ℝ)*X 1 1+(3700277809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3141542487/5000000000 : ℝ)*X 2 0+(-3596266909/10000000000 : ℝ)*X 2 1+(-2231750767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-94323613/250000000 : ℝ)*X 0 0+(-4838523883/10000000000 : ℝ)*X 0 1+(5959587/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((132522463/400000000 : ℝ)*X 1 0+(10833467/20000000 : ℝ)*X 1 1+(3554147443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((6057969913/10000000000 : ℝ)*X 2 0+(-1793703583/5000000000 : ℝ)*X 2 1+(-39441239/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1913243/5000000000 : ℝ)*X 0 0+(-1387064201/10000000000 : ℝ)*X 0 1+(9294894669/10000000000 : ℝ)*X 0 2+(-1913243/5000000000 : ℝ)*X 1 0+(-1387064201/10000000000 : ℝ)*X 1 1+(9294894669/10000000000 : ℝ)*X 1 2+(-1913243/5000000000 : ℝ)*X 2 0+(-1387064201/10000000000 : ℝ)*X 2 1+(9294894669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3246817667/10000000000 : ℝ)*X 0 0+(-3082153459/10000000000 : ℝ)*X 0 1+(2945228291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5111414987/10000000000 : ℝ)*X 1 0+(4585503023/10000000000 : ℝ)*X 1 1+(1274443203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1517335933/2000000000 : ℝ)*X 2 0+(-358467969/1250000000 : ℝ)*X 2 1+(-1261495813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-22413/2500000000 : ℝ)*X 0 0+(-218903029/1250000000 : ℝ)*X 0 1+(181132277/200000000 : ℝ)*X 0 2+(-22413/2500000000 : ℝ)*X 1 0+(-218903029/1250000000 : ℝ)*X 1 1+(181132277/200000000 : ℝ)*X 1 2+(-22413/2500000000 : ℝ)*X 2 0+(-218903029/1250000000 : ℝ)*X 2 1+(181132277/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-3317685303/10000000000 : ℝ)*X 0 0+(-857411857/2000000000 : ℝ)*X 0 1+(59042181/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2953167469/10000000000 : ℝ)*X 1 0+(5465298541/10000000000 : ℝ)*X 1 1+(480843691/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((354806653/500000000 : ℝ)*X 2 0+(-735496199/2500000000 : ℝ)*X 2 1+(-942466581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((16957/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16957/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1202484259203744766281/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (251310624601/1000000000000 : ℝ)*(base1) + (178084796859/250000000000 : ℝ)*(base7) + (56439/1000000000000 : ℝ)*(base22) + (114647484957/1000000000000 : ℝ)*(base54) + (212110230889/200000000000 : ℝ)*(base60) + (3432797523959/1000000000000 : ℝ)*(major_s0_0) + (3432797523959/1000000000000 : ℝ)*(major_s0_1) + (1659075019501/500000000000 : ℝ)*(major_s0_2) + (4939964479673/1000000000000 : ℝ)*(sp_s0_7) + (4688660034169/1000000000000 : ℝ)*(sp_s0_8) + (4574012492773/1000000000000 : ℝ)*(sp_s0_9) + (1062513394897/500000000000 : ℝ)*(sp_s0_13) + (9801779/100000000000 : ℝ)*(sp_s0_20) + (6179097/1000000000000 : ℝ)*(sp_s0_21) + (889371864853/500000000000 : ℝ)*(f.failure) + (4688660034169/1000000000000 : ℝ)*(f.sum) + (99269927994501/10000000000000000000000000000 : ℝ)*base62 + (77690607294573/1000000000000000000000000000 : ℝ)*base65 + (505473559771247/2500000000000000000000000000 : ℝ)*base66 + (105747904601933/1250000000000000000000000000 : ℝ)*base69 + (1163002775430371/5000000000000000000000000000 : ℝ)*base71 + (58583372438007/2000000000000000000000000000 : ℝ)*base72 + (530598304838007/2000000000000000000000000000 : ℝ)*base75 + (957644981521247/2500000000000000000000000000 : ℝ)*base76 + (835027694724977/10000000000000000000000000000 : ℝ)*base79 + (3047/5000000000000000 : ℝ)*base87 + (3047/5000000000000000 : ℝ)*base89 + (3047/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-2607/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-2607/4000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (86325166154467857/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (741671454427/1000000000000 : ℝ)*(base1) + (1287012141473/1000000000000 : ℝ)*(base7) + (153614906557/500000000000 : ℝ)*(base40) + (38248183897/62500000000 : ℝ)*(base60) + (1249175801737/500000000000 : ℝ)*(major_s0_0) + (1249175801737/500000000000 : ℝ)*(major_s0_1) + (1249175801737/500000000000 : ℝ)*(major_s0_2) + (55370577/1000000000000 : ℝ)*(sp_s0_1) + (436287523/1000000000000 : ℝ)*(sp_s0_13) + (58193628409/15625000000 : ℝ)*(sp_s0_14) + (2982665393171/1000000000000 : ℝ)*(sp_s0_15) + (2982704510973/1000000000000 : ℝ)*(sp_s0_16) + (1839454170741/1000000000000 : ℝ)*(sp_s0_20) + (650111/40000000000 : ℝ)*(sp_s0_23) + (647274885609/500000000000 : ℝ)*(f.failure) + (2982720763749/1000000000000 : ℝ)*(f.sum) + (992229317661489/5000000000000000000000000000 : ℝ)*base63 + (591903626746199/1000000000000000000000000000 : ℝ)*base64 + (491922976401879/1250000000000000000000000000 : ℝ)*base67 + (961984231973121/1250000000000000000000000000 : ℝ)*base69 + (108364032876521/5000000000000000000000000000 : ℝ)*base71 + (691993013046199/1000000000000000000000000000 : ℝ)*base73 + (743033367853801/1000000000000000000000000000 : ℝ)*base75 + (649530548598121/1250000000000000000000000000 : ℝ)*base76 + (459832964338511/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1909/5000000000000000 : ℝ)*base86 + (1909/5000000000000000 : ℝ)*base88 + (1909/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7951/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7951/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3906721781674988531637/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2848941047097/1000000000000 : ℝ)*(base1) + (236437658483/200000000000 : ℝ)*(base7) + (771459366739/500000000000 : ℝ)*(base40) + (538328253951/1000000000000 : ℝ)*(base60) + (160833307063/50000000000 : ℝ)*(major_s0_0) + (160833307063/50000000000 : ℝ)*(major_s0_1) + (160833307063/50000000000 : ℝ)*(major_s0_2) + (64749717/1000000000000 : ℝ)*(sp_s0_2) + (1179269/125000000000 : ℝ)*(sp_s0_7) + (37204401/500000000000 : ℝ)*(sp_s0_8) + (48493787/500000000000 : ℝ)*(sp_s0_16) + (21733357807/3125000000 : ℝ)*(sp_s0_21) + (4105668476493/1000000000000 : ℝ)*(sp_s0_22) + (1026395287001/250000000000 : ℝ)*(sp_s0_23) + (833376377341/500000000000 : ℝ)*(f.failure) + (821148577059/200000000000 : ℝ)*(f.sum) + (64752108092111/500000000000000000000000000 : ℝ)*base63 + (27507004548599/100000000000000000000000000 : ℝ)*base65 + (45177109537279/125000000000000000000000000 : ℝ)*base66 + (21038135050221/125000000000000000000000000 : ℝ)*base68 + (294150621856121/500000000000000000000000000 : ℝ)*base70 + (22334715711401/100000000000000000000000000 : ℝ)*base73 + (28396574691401/100000000000000000000000000 : ℝ)*base74 + (37695487224779/125000000000000000000000000 : ℝ)*base76 + (220154542357889/500000000000000000000000000 : ℝ)*base79 + (3959/5000000000000000 : ℝ)*base87 + (3959/5000000000000000 : ℝ)*base89 + (3959/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (16957/50000 : ℝ) ^ (41/8 : ℝ) ≤ (391915514672236091/100000000000000000000 : ℝ) := by
    have hpowers : (16957/50000 : ℝ)^41 ≤ (391915514672236091/100000000000000000000 : ℝ)^8 := by
      have hnat : (16957 : ℕ)^41*100000000000000000000^8 ≤ 391915514672236091^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16957 50000 391915514672236091 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16957/50000 : ℝ)) (X := (391915514672236091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100391915514672236091/100000000000000000000 : ℝ) ≤ (10007635099137443/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100391915514672236091/100000000000000000000 : ℝ)^8 ≤ (10007635099137443/10000000000000000 : ℝ)^41 := by
      have hnat : (100391915514672236091 : ℕ)^8*10000000000000000^41 ≤ 10007635099137443^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100391915514672236091 100000000000000000000 10007635099137443 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007635099137443/10000000000000000 : ℝ)) (X := (100391915514672236091/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50391915514672236091/50000000000000000000 : ℝ) ≤ (2003049249077221/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50391915514672236091/50000000000000000000 : ℝ)^8 ≤ (2003049249077221/2000000000000000 : ℝ)^41 := by
      have hnat : (50391915514672236091 : ℕ)^8*2000000000000000^41 ≤ 2003049249077221^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50391915514672236091 50000000000000000000 2003049249077221 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003049249077221/2000000000000000 : ℝ)) (X := (50391915514672236091/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7635099137443/3391400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3805573124331/1695700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (16957/50000 : ℝ)) (alpha := (7635099137443/3391400000000000 : ℝ)) (beta := (3805573124331/1695700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16957/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7635099137443/3391400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3805573124331/1695700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2607/4000 : ℝ) ^ (41/8 : ℝ) ≤ (11147188090122501879/100000000000000000000 : ℝ) := by
    have hpowers : (2607/4000 : ℝ)^41 ≤ (11147188090122501879/100000000000000000000 : ℝ)^8 := by
      have hnat : (2607 : ℕ)^41*100000000000000000000^8 ≤ 11147188090122501879^8*4000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2607 4000 11147188090122501879 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2607/4000 : ℝ)) (X := (11147188090122501879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (111147188090122501879/100000000000000000000 : ℝ) ≤ (5104177929561749/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (111147188090122501879/100000000000000000000 : ℝ)^8 ≤ (5104177929561749/5000000000000000 : ℝ)^41 := by
      have hnat : (111147188090122501879 : ℕ)^8*5000000000000000^41 ≤ 5104177929561749^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111147188090122501879 100000000000000000000 5104177929561749 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5104177929561749/5000000000000000 : ℝ)) (X := (111147188090122501879/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (61147188090122501879/50000000000000000000 : ℝ) ≤ (10400516901832517/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (61147188090122501879/50000000000000000000 : ℝ)^8 ≤ (10400516901832517/10000000000000000 : ℝ)^41 := by
      have hnat : (61147188090122501879 : ℕ)^8*10000000000000000^41 ≤ 10400516901832517^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61147188090122501879 50000000000000000000 10400516901832517 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10400516901832517/10000000000000000 : ℝ)) (X := (61147188090122501879/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(34725976520583/1086250000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(192161042709019/6517500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (2607/4000 : ℝ)) (alpha := (34725976520583/1086250000000000 : ℝ)) (beta := (192161042709019/6517500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (2607/4000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(34725976520583/1086250000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(192161042709019/6517500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7951/20000 : ℝ) ^ (41/8 : ℝ) ≤ (221219174491164897/25000000000000000000 : ℝ) := by
    have hpowers : (7951/20000 : ℝ)^41 ≤ (221219174491164897/25000000000000000000 : ℝ)^8 := by
      have hnat : (7951 : ℕ)^41*25000000000000000000^8 ≤ 221219174491164897^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7951 20000 221219174491164897 25000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7951/20000 : ℝ)) (X := (221219174491164897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25221219174491164897/25000000000000000000 : ℝ) ≤ (626075295421027/625000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25221219174491164897/25000000000000000000 : ℝ)^8 ≤ (626075295421027/625000000000000 : ℝ)^41 := by
      have hnat : (25221219174491164897 : ℕ)^8*625000000000000^41 ≤ 626075295421027^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25221219174491164897 25000000000000000000 626075295421027 625000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626075295421027/625000000000000 : ℝ)) (X := (25221219174491164897/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12721219174491164897/12500000000000000000 : ℝ) ≤ (2508572104669297/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (12721219174491164897/12500000000000000000 : ℝ)^8 ≤ (2508572104669297/2500000000000000 : ℝ)^41 := by
      have hnat : (12721219174491164897 : ℕ)^8*2500000000000000^41 ≤ 2508572104669297^41*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12721219174491164897 12500000000000000000 2508572104669297 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508572104669297/2500000000000000 : ℝ)) (X := (12721219174491164897/12500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1075295421027/248468750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(4270922985189/993875000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (7951/20000 : ℝ)) (alpha := (1075295421027/248468750000000 : ℝ)) (beta := (4270922985189/993875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7951/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1075295421027/248468750000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(4270922985189/993875000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-860006557/2500000000 : ℝ)*X 0 0+(-757372747/2000000000 : ℝ)*X 0 1+(5088857221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2094433249/5000000000 : ℝ)*X 1 0+(4622628393/10000000000 : ℝ)*X 1 1+(3529532819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5006551521/10000000000 : ℝ)*X 2 0+(-1040319461/2500000000 : ℝ)*X 2 1+(-3139501087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3088681719/10000000000 : ℝ)*X 0 0+(-3190785037/10000000000 : ℝ)*X 0 1+(296666389/500000000 : ℝ)*X 0 2+(3088681719/10000000000 : ℝ)*X 1 0+(-3190785037/10000000000 : ℝ)*X 1 1+(296666389/500000000 : ℝ)*X 1 2+(3088681719/10000000000 : ℝ)*X 2 0+(-3190785037/10000000000 : ℝ)*X 2 1+(296666389/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-2461575107584927230904692407012409/292907544957500000000000000000000 : ℝ) := by norm_num
    linear_combination (323083065731/1000000000000 : ℝ)*(base1) + (46793/1000000000000 : ℝ)*(base19) + (3503/1000000000000 : ℝ)*(base21) + (2267/1000000000000 : ℝ)*(base39) + (543862342719/1000000000000 : ℝ)*(base40) + (65357600363/250000000000 : ℝ)*(base49) + (2409/100000000000 : ℝ)*(base50) + (21561530739/40000000000 : ℝ)*(base60) + (19299/10000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (3124393752281/1000000000000 : ℝ)*(sp_s1_0) + (2801310639757/1000000000000 : ℝ)*(sp_s1_1) + (1400655341523/500000000000 : ℝ)*(sp_s1_2) + (676916934269/1000000000000 : ℝ)*(sp_s1_6) + (2801310686549/1000000000000 : ℝ)*(f.sum) + (4643262655468717/69094190000000000000000000000 : ℝ)*base62 + (1046954242761/9938750000000000000000000 : ℝ)*base65 + (4956877247349/8690000000000000000000000 : ℝ)*base66 + (11050825795547/79510000000000000000000000 : ℝ)*base68 + (232556728301116909/337062767500000000000000000000 : ℝ)*base70 + (73732629405471/169570000000000000000000000 : ℝ)*base72 + (11921343387/8690000000000000000000000 : ℝ)*base75 + (59242647319411/169570000000000000000000000 : ℝ)*base76 + (22555896184720397/73678165000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p022_b039 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c322070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c322071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_b039 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
