-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:50.9786+00:00
-- url     : https://prove2.me/submissions/30da4047-76c0-4f0b-8c5d-49c403752851

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
theorem collision_support_c326039_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-35174501/312500000 : ℝ)*x 0 + (-6146613531/10000000000 : ℝ)*x 1 + (4500415239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35174501/312500000 : ℝ)^89 ≤ (3486829890289/50000000000000 : ℝ)^73 := by
    have hnat : (35174501 : ℕ)^89*50000000000000^73 ≤ 3486829890289^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35174501 312500000 3486829890289 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6146613531/10000000000 : ℝ)^89 ≤ (6905888216401/12500000000000 : ℝ)^73 := by
    have hnat : (6146613531 : ℕ)^89*12500000000000^73 ≤ 6905888216401^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6146613531 10000000000 6905888216401 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500415239/10000000000 : ℝ)^89 ≤ (37779234475331/100000000000000 : ℝ)^73 := by
    have hnat : (4500415239 : ℕ)^89*100000000000000^73 ≤ 37779234475331^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500415239 10000000000 37779234475331 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35174501/312500000 : ℝ), (-6146613531/10000000000 : ℝ), (4500415239/10000000000 : ℝ)] ![(3486829890289/50000000000000 : ℝ), (6905888216401/12500000000000 : ℝ), (37779234475331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35174501/312500000 : ℝ)|^89 ≤ (3486829890289/50000000000000 : ℝ)^73
        have hw : |(-35174501/312500000 : ℝ)|=(35174501/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6146613531/10000000000 : ℝ)|^89 ≤ (6905888216401/12500000000000 : ℝ)^73
        have hw : |(-6146613531/10000000000 : ℝ)|=(6146613531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500415239/10000000000 : ℝ)|^89 ≤ (37779234475331/100000000000000 : ℝ)^73
        have hw : |(4500415239/10000000000 : ℝ)|=(4500415239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4697435157/10000000000 : ℝ)*x 0 + (1846540519/5000000000 : ℝ)*x 1 + (755314969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4697435157/10000000000 : ℝ)^89 ≤ (39805205645349/100000000000000 : ℝ)^73 := by
    have hnat : (4697435157 : ℕ)^89*100000000000000^73 ≤ 39805205645349^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4697435157 10000000000 39805205645349 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846540519/5000000000 : ℝ)^89 ≤ (29687248831779/100000000000000 : ℝ)^73 := by
    have hnat : (1846540519 : ℕ)^89*100000000000000^73 ≤ 29687248831779^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846540519 5000000000 29687248831779 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755314969/2000000000 : ℝ)^89 ≤ (15253772754817/50000000000000 : ℝ)^73 := by
    have hnat : (755314969 : ℕ)^89*50000000000000^73 ≤ 15253772754817^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755314969 2000000000 15253772754817 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4697435157/10000000000 : ℝ), (1846540519/5000000000 : ℝ), (755314969/2000000000 : ℝ)] ![(39805205645349/100000000000000 : ℝ), (29687248831779/100000000000000 : ℝ), (15253772754817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4697435157/10000000000 : ℝ)|^89 ≤ (39805205645349/100000000000000 : ℝ)^73
        have hw : |(4697435157/10000000000 : ℝ)|=(4697435157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846540519/5000000000 : ℝ)|^89 ≤ (29687248831779/100000000000000 : ℝ)^73
        have hw : |(1846540519/5000000000 : ℝ)|=(1846540519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755314969/2000000000 : ℝ)|^89 ≤ (15253772754817/50000000000000 : ℝ)^73
        have hw : |(755314969/2000000000 : ℝ)|=(755314969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-159316259/5000000000 : ℝ)*x 0 + (-3893388461/5000000000 : ℝ)*x 1 + (3185411353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159316259/5000000000 : ℝ)^89 ≤ (374269207703/25000000000000 : ℝ)^73 := by
    have hnat : (159316259 : ℕ)^89*25000000000000^73 ≤ 374269207703^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159316259 5000000000 374269207703 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3893388461/5000000000 : ℝ)^89 ≤ (2948531152791/4000000000000 : ℝ)^73 := by
    have hnat : (3893388461 : ℕ)^89*4000000000000^73 ≤ 2948531152791^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893388461 5000000000 2948531152791 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185411353/10000000000 : ℝ)^89 ≤ (24789644336201/100000000000000 : ℝ)^73 := by
    have hnat : (3185411353 : ℕ)^89*100000000000000^73 ≤ 24789644336201^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185411353 10000000000 24789644336201 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159316259/5000000000 : ℝ), (-3893388461/5000000000 : ℝ), (3185411353/10000000000 : ℝ)] ![(374269207703/25000000000000 : ℝ), (2948531152791/4000000000000 : ℝ), (24789644336201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159316259/5000000000 : ℝ)|^89 ≤ (374269207703/25000000000000 : ℝ)^73
        have hw : |(-159316259/5000000000 : ℝ)|=(159316259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3893388461/5000000000 : ℝ)|^89 ≤ (2948531152791/4000000000000 : ℝ)^73
        have hw : |(-3893388461/5000000000 : ℝ)|=(3893388461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185411353/10000000000 : ℝ)|^89 ≤ (24789644336201/100000000000000 : ℝ)^73
        have hw : |(3185411353/10000000000 : ℝ)|=(3185411353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1557543761/5000000000 : ℝ)*x 0 + (426853807/1000000000 : ℝ)*x 1 + (297522837/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557543761/5000000000 : ℝ)^89 ≤ (24124039710593/100000000000000 : ℝ)^73 := by
    have hnat : (1557543761 : ℕ)^89*100000000000000^73 ≤ 24124039710593^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557543761 5000000000 24124039710593 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426853807/1000000000 : ℝ)^89 ≤ (35419665406421/100000000000000 : ℝ)^73 := by
    have hnat : (426853807 : ℕ)^89*100000000000000^73 ≤ 35419665406421^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426853807 1000000000 35419665406421 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297522837/625000000 : ℝ)^89 ≤ (40456294867449/100000000000000 : ℝ)^73 := by
    have hnat : (297522837 : ℕ)^89*100000000000000^73 ≤ 40456294867449^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297522837 625000000 40456294867449 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1557543761/5000000000 : ℝ), (426853807/1000000000 : ℝ), (297522837/625000000 : ℝ)] ![(24124039710593/100000000000000 : ℝ), (35419665406421/100000000000000 : ℝ), (40456294867449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1557543761/5000000000 : ℝ)|^89 ≤ (24124039710593/100000000000000 : ℝ)^73
        have hw : |(1557543761/5000000000 : ℝ)|=(1557543761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(426853807/1000000000 : ℝ)|^89 ≤ (35419665406421/100000000000000 : ℝ)^73
        have hw : |(426853807/1000000000 : ℝ)|=(426853807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297522837/625000000 : ℝ)|^89 ≤ (40456294867449/100000000000000 : ℝ)^73
        have hw : |(297522837/625000000 : ℝ)|=(297522837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (963938853/2000000000 : ℝ)*x 0 + (-268379363/1000000000 : ℝ)*x 1 + (-4601085849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963938853/2000000000 : ℝ)^89 ≤ (20535927095489/50000000000000 : ℝ)^73 := by
    have hnat : (963938853 : ℕ)^89*50000000000000^73 ≤ 20535927095489^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963938853 2000000000 20535927095489 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268379363/1000000000 : ℝ)^89 ≤ (2011608420719/10000000000000 : ℝ)^73 := by
    have hnat : (268379363 : ℕ)^89*10000000000000^73 ≤ 2011608420719^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268379363 1000000000 2011608420719 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4601085849/10000000000 : ℝ)^89 ≤ (38812061576727/100000000000000 : ℝ)^73 := by
    have hnat : (4601085849 : ℕ)^89*100000000000000^73 ≤ 38812061576727^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601085849 10000000000 38812061576727 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963938853/2000000000 : ℝ), (-268379363/1000000000 : ℝ), (-4601085849/10000000000 : ℝ)] ![(20535927095489/50000000000000 : ℝ), (2011608420719/10000000000000 : ℝ), (38812061576727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963938853/2000000000 : ℝ)|^89 ≤ (20535927095489/50000000000000 : ℝ)^73
        have hw : |(963938853/2000000000 : ℝ)|=(963938853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268379363/1000000000 : ℝ)|^89 ≤ (2011608420719/10000000000000 : ℝ)^73
        have hw : |(-268379363/1000000000 : ℝ)|=(268379363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4601085849/10000000000 : ℝ)|^89 ≤ (38812061576727/100000000000000 : ℝ)^73
        have hw : |(-4601085849/10000000000 : ℝ)|=(4601085849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6535965213/10000000000 : ℝ)*x 0 + (691771/10000000000 : ℝ)*x 1 + (297522837/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6535965213/10000000000 : ℝ)^89 ≤ (29771428779513/50000000000000 : ℝ)^73 := by
    have hnat : (6535965213 : ℕ)^89*50000000000000^73 ≤ 29771428779513^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6535965213 10000000000 29771428779513 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691771/10000000000 : ℝ)^89 ≤ (211891379/25000000000000 : ℝ)^73 := by
    have hnat : (691771 : ℕ)^89*25000000000000^73 ≤ 211891379^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691771 10000000000 211891379 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297522837/625000000 : ℝ)^89 ≤ (40456294867449/100000000000000 : ℝ)^73 := by
    have hnat : (297522837 : ℕ)^89*100000000000000^73 ≤ 40456294867449^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297522837 625000000 40456294867449 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6535965213/10000000000 : ℝ), (691771/10000000000 : ℝ), (297522837/625000000 : ℝ)] ![(29771428779513/50000000000000 : ℝ), (211891379/25000000000000 : ℝ), (40456294867449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6535965213/10000000000 : ℝ)|^89 ≤ (29771428779513/50000000000000 : ℝ)^73
        have hw : |(6535965213/10000000000 : ℝ)|=(6535965213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(691771/10000000000 : ℝ)|^89 ≤ (211891379/25000000000000 : ℝ)^73
        have hw : |(691771/10000000000 : ℝ)|=(691771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297522837/625000000 : ℝ)|^89 ≤ (40456294867449/100000000000000 : ℝ)^73
        have hw : |(297522837/625000000 : ℝ)|=(297522837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-32515541/2500000000 : ℝ)*x 0 + (-2773107669/5000000000 : ℝ)*x 1 + (716730561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32515541/2500000000 : ℝ)^89 ≤ (502127726757/100000000000000 : ℝ)^73 := by
    have hnat : (32515541 : ℕ)^89*100000000000000^73 ≤ 502127726757^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32515541 2500000000 502127726757 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2773107669/5000000000 : ℝ)^89 ≤ (2437005030037/5000000000000 : ℝ)^73 := by
    have hnat : (2773107669 : ℕ)^89*5000000000000^73 ≤ 2437005030037^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773107669 5000000000 2437005030037 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716730561/1250000000 : ℝ)^89 ≤ (25378885832831/50000000000000 : ℝ)^73 := by
    have hnat : (716730561 : ℕ)^89*50000000000000^73 ≤ 25378885832831^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716730561 1250000000 25378885832831 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32515541/2500000000 : ℝ), (-2773107669/5000000000 : ℝ), (716730561/1250000000 : ℝ)] ![(502127726757/100000000000000 : ℝ), (2437005030037/5000000000000 : ℝ), (25378885832831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32515541/2500000000 : ℝ)|^89 ≤ (502127726757/100000000000000 : ℝ)^73
        have hw : |(-32515541/2500000000 : ℝ)|=(32515541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2773107669/5000000000 : ℝ)|^89 ≤ (2437005030037/5000000000000 : ℝ)^73
        have hw : |(-2773107669/5000000000 : ℝ)|=(2773107669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(716730561/1250000000 : ℝ)|^89 ≤ (25378885832831/50000000000000 : ℝ)^73
        have hw : |(716730561/1250000000 : ℝ)|=(716730561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (358358231/1000000000 : ℝ)*x 0 + (2034186441/5000000000 : ℝ)*x 1 + (2259872529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358358231/1000000000 : ℝ)^89 ≤ (28617620689209/100000000000000 : ℝ)^73 := by
    have hnat : (358358231 : ℕ)^89*100000000000000^73 ≤ 28617620689209^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358358231 1000000000 28617620689209 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034186441/5000000000 : ℝ)^89 ≤ (33405220290847/100000000000000 : ℝ)^73 := by
    have hnat : (2034186441 : ℕ)^89*100000000000000^73 ≤ 33405220290847^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034186441 5000000000 33405220290847 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259872529/5000000000 : ℝ)^89 ≤ (37977159016269/100000000000000 : ℝ)^73 := by
    have hnat : (2259872529 : ℕ)^89*100000000000000^73 ≤ 37977159016269^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259872529 5000000000 37977159016269 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(358358231/1000000000 : ℝ), (2034186441/5000000000 : ℝ), (2259872529/5000000000 : ℝ)] ![(28617620689209/100000000000000 : ℝ), (33405220290847/100000000000000 : ℝ), (37977159016269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(358358231/1000000000 : ℝ)|^89 ≤ (28617620689209/100000000000000 : ℝ)^73
        have hw : |(358358231/1000000000 : ℝ)|=(358358231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2034186441/5000000000 : ℝ)|^89 ≤ (33405220290847/100000000000000 : ℝ)^73
        have hw : |(2034186441/5000000000 : ℝ)|=(2034186441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259872529/5000000000 : ℝ)|^89 ≤ (37977159016269/100000000000000 : ℝ)^73
        have hw : |(2259872529/5000000000 : ℝ)|=(2259872529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (11792499/19531250 : ℝ)*x 0 + (-2733835119/10000000000 : ℝ)*x 1 + (-162317921/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11792499/19531250 : ℝ)^89 ≤ (54056582916423/100000000000000 : ℝ)^73 := by
    have hnat : (11792499 : ℕ)^89*100000000000000^73 ≤ 54056582916423^73*19531250^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11792499 19531250 54056582916423 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733835119/10000000000 : ℝ)^89 ≤ (5143576029441/25000000000000 : ℝ)^73 := by
    have hnat : (2733835119 : ℕ)^89*25000000000000^73 ≤ 5143576029441^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733835119 10000000000 5143576029441 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162317921/500000000 : ℝ)^89 ≤ (158556955889/625000000000 : ℝ)^73 := by
    have hnat : (162317921 : ℕ)^89*625000000000^73 ≤ 158556955889^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162317921 500000000 158556955889 625000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(11792499/19531250 : ℝ), (-2733835119/10000000000 : ℝ), (-162317921/500000000 : ℝ)] ![(54056582916423/100000000000000 : ℝ), (5143576029441/25000000000000 : ℝ), (158556955889/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(11792499/19531250 : ℝ)|^89 ≤ (54056582916423/100000000000000 : ℝ)^73
        have hw : |(11792499/19531250 : ℝ)|=(11792499/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2733835119/10000000000 : ℝ)|^89 ≤ (5143576029441/25000000000000 : ℝ)^73
        have hw : |(-2733835119/10000000000 : ℝ)|=(2733835119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-162317921/500000000 : ℝ)|^89 ≤ (158556955889/625000000000 : ℝ)^73
        have hw : |(-162317921/500000000 : ℝ)|=(162317921/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2283681053/2500000000 : ℝ)*x 0 + (-885703/10000000000 : ℝ)*x 1 + (391966871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2283681053/2500000000 : ℝ)^89 ≤ (17910624859171/20000000000000 : ℝ)^73 := by
    have hnat : (2283681053 : ℕ)^89*20000000000000^73 ≤ 17910624859171^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283681053 2500000000 17910624859171 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885703/10000000000 : ℝ)^89 ≤ (1145572283/100000000000000 : ℝ)^73 := by
    have hnat : (885703 : ℕ)^89*100000000000000^73 ≤ 1145572283^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885703 10000000000 1145572283 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391966871/2500000000 : ℝ)^89 ≤ (10445730111499/100000000000000 : ℝ)^73 := by
    have hnat : (391966871 : ℕ)^89*100000000000000^73 ≤ 10445730111499^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391966871 2500000000 10445730111499 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2283681053/2500000000 : ℝ), (-885703/10000000000 : ℝ), (391966871/2500000000 : ℝ)] ![(17910624859171/20000000000000 : ℝ), (1145572283/100000000000000 : ℝ), (10445730111499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2283681053/2500000000 : ℝ)|^89 ≤ (17910624859171/20000000000000 : ℝ)^73
        have hw : |(2283681053/2500000000 : ℝ)|=(2283681053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885703/10000000000 : ℝ)|^89 ≤ (1145572283/100000000000000 : ℝ)^73
        have hw : |(-885703/10000000000 : ℝ)|=(885703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(391966871/2500000000 : ℝ)|^89 ≤ (10445730111499/100000000000000 : ℝ)^73
        have hw : |(391966871/2500000000 : ℝ)|=(391966871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-694991671/10000000000 : ℝ)*x 0 + (-1550837053/2000000000 : ℝ)*x 1 + (2972929873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (694991671/10000000000 : ℝ)^89 ≤ (3874065056409/100000000000000 : ℝ)^73 := by
    have hnat : (694991671 : ℕ)^89*100000000000000^73 ≤ 3874065056409^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694991671 10000000000 3874065056409 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1550837053/2000000000 : ℝ)^89 ≤ (73337301094731/100000000000000 : ℝ)^73 := by
    have hnat : (1550837053 : ℕ)^89*100000000000000^73 ≤ 73337301094731^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550837053 2000000000 73337301094731 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2972929873/10000000000 : ℝ)^89 ≤ (712144807173/3125000000000 : ℝ)^73 := by
    have hnat : (2972929873 : ℕ)^89*3125000000000^73 ≤ 712144807173^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972929873 10000000000 712144807173 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-694991671/10000000000 : ℝ), (-1550837053/2000000000 : ℝ), (2972929873/10000000000 : ℝ)] ![(3874065056409/100000000000000 : ℝ), (73337301094731/100000000000000 : ℝ), (712144807173/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-694991671/10000000000 : ℝ)|^89 ≤ (3874065056409/100000000000000 : ℝ)^73
        have hw : |(-694991671/10000000000 : ℝ)|=(694991671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1550837053/2000000000 : ℝ)|^89 ≤ (73337301094731/100000000000000 : ℝ)^73
        have hw : |(-1550837053/2000000000 : ℝ)|=(1550837053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2972929873/10000000000 : ℝ)|^89 ≤ (712144807173/3125000000000 : ℝ)^73
        have hw : |(2972929873/10000000000 : ℝ)|=(2972929873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (612931547/1000000000 : ℝ)*x 0 + (128521599/400000000 : ℝ)*x 1 + (1329533763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612931547/1000000000 : ℝ)^89 ≤ (55057607947649/100000000000000 : ℝ)^73 := by
    have hnat : (612931547 : ℕ)^89*100000000000000^73 ≤ 55057607947649^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612931547 1000000000 55057607947649 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128521599/400000000 : ℝ)^89 ≤ (391437994453/1562500000000 : ℝ)^73 := by
    have hnat : (128521599 : ℕ)^89*1562500000000^73 ≤ 391437994453^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128521599 400000000 391437994453 1562500000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1329533763/5000000000 : ℝ)^89 ≤ (19890360383427/100000000000000 : ℝ)^73 := by
    have hnat : (1329533763 : ℕ)^89*100000000000000^73 ≤ 19890360383427^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329533763 5000000000 19890360383427 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(612931547/1000000000 : ℝ), (128521599/400000000 : ℝ), (1329533763/5000000000 : ℝ)] ![(55057607947649/100000000000000 : ℝ), (391437994453/1562500000000 : ℝ), (19890360383427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(612931547/1000000000 : ℝ)|^89 ≤ (55057607947649/100000000000000 : ℝ)^73
        have hw : |(612931547/1000000000 : ℝ)|=(612931547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128521599/400000000 : ℝ)|^89 ≤ (391437994453/1562500000000 : ℝ)^73
        have hw : |(128521599/400000000 : ℝ)|=(128521599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1329533763/5000000000 : ℝ)|^89 ≤ (19890360383427/100000000000000 : ℝ)^73
        have hw : |(1329533763/5000000000 : ℝ)|=(1329533763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1241479581/5000000000 : ℝ)*x 0 + (-5763061189/10000000000 : ℝ)*x 1 + (-3789060903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1241479581/5000000000 : ℝ)^89 ≤ (4574042309213/25000000000000 : ℝ)^73 := by
    have hnat : (1241479581 : ℕ)^89*25000000000000^73 ≤ 4574042309213^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241479581 5000000000 4574042309213 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5763061189/10000000000 : ℝ)^89 ≤ (51073270011019/100000000000000 : ℝ)^73 := by
    have hnat : (5763061189 : ℕ)^89*100000000000000^73 ≤ 51073270011019^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5763061189 10000000000 51073270011019 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3789060903/10000000000 : ℝ)^89 ≤ (30630560732259/100000000000000 : ℝ)^73 := by
    have hnat : (3789060903 : ℕ)^89*100000000000000^73 ≤ 30630560732259^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789060903 10000000000 30630560732259 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1241479581/5000000000 : ℝ), (-5763061189/10000000000 : ℝ), (-3789060903/10000000000 : ℝ)] ![(4574042309213/25000000000000 : ℝ), (51073270011019/100000000000000 : ℝ), (30630560732259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1241479581/5000000000 : ℝ)|^89 ≤ (4574042309213/25000000000000 : ℝ)^73
        have hw : |(1241479581/5000000000 : ℝ)|=(1241479581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5763061189/10000000000 : ℝ)|^89 ≤ (51073270011019/100000000000000 : ℝ)^73
        have hw : |(-5763061189/10000000000 : ℝ)|=(5763061189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3789060903/10000000000 : ℝ)|^89 ≤ (30630560732259/100000000000000 : ℝ)^73
        have hw : |(-3789060903/10000000000 : ℝ)|=(3789060903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (419834393/500000000 : ℝ)*x 0 + (17/1250000000 : ℝ)*x 1 + (40341233/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419834393/500000000 : ℝ)^89 ≤ (20202920579193/25000000000000 : ℝ)^73 := by
    have hnat : (419834393 : ℕ)^89*25000000000000^73 ≤ 20202920579193^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419834393 500000000 20202920579193 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17/1250000000 : ℝ)^89 ≤ (6417/25000000000000 : ℝ)^73 := by
    have hnat : (17 : ℕ)^89*25000000000000^73 ≤ 6417^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17 1250000000 6417 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40341233/156250000 : ℝ)^89 ≤ (19188317640317/100000000000000 : ℝ)^73 := by
    have hnat : (40341233 : ℕ)^89*100000000000000^73 ≤ 19188317640317^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40341233 156250000 19188317640317 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419834393/500000000 : ℝ), (17/1250000000 : ℝ), (40341233/156250000 : ℝ)] ![(20202920579193/25000000000000 : ℝ), (6417/25000000000000 : ℝ), (19188317640317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419834393/500000000 : ℝ)|^89 ≤ (20202920579193/25000000000000 : ℝ)^73
        have hw : |(419834393/500000000 : ℝ)|=(419834393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17/1250000000 : ℝ)|^89 ≤ (6417/25000000000000 : ℝ)^73
        have hw : |(17/1250000000 : ℝ)|=(17/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40341233/156250000 : ℝ)|^89 ≤ (19188317640317/100000000000000 : ℝ)^73
        have hw : |(40341233/156250000 : ℝ)|=(40341233/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079031663/10000000000 : ℝ)*x 0 + (-1271767241/2500000000 : ℝ)*x 1 + (2425560213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079031663/10000000000 : ℝ)^89 ≤ (1841879530543/12500000000000 : ℝ)^73 := by
    have hnat : (2079031663 : ℕ)^89*12500000000000^73 ≤ 1841879530543^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079031663 10000000000 1841879530543 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271767241/2500000000 : ℝ)^89 ≤ (1370824267291/3125000000000 : ℝ)^73 := by
    have hnat : (1271767241 : ℕ)^89*3125000000000^73 ≤ 1370824267291^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271767241 2500000000 1370824267291 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2425560213/5000000000 : ℝ)^89 ≤ (1655943487369/4000000000000 : ℝ)^73 := by
    have hnat : (2425560213 : ℕ)^89*4000000000000^73 ≤ 1655943487369^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425560213 5000000000 1655943487369 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079031663/10000000000 : ℝ), (-1271767241/2500000000 : ℝ), (2425560213/5000000000 : ℝ)] ![(1841879530543/12500000000000 : ℝ), (1370824267291/3125000000000 : ℝ), (1655943487369/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079031663/10000000000 : ℝ)|^89 ≤ (1841879530543/12500000000000 : ℝ)^73
        have hw : |(-2079031663/10000000000 : ℝ)|=(2079031663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1271767241/2500000000 : ℝ)|^89 ≤ (1370824267291/3125000000000 : ℝ)^73
        have hw : |(-1271767241/2500000000 : ℝ)|=(1271767241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2425560213/5000000000 : ℝ)|^89 ≤ (1655943487369/4000000000000 : ℝ)^73
        have hw : |(2425560213/5000000000 : ℝ)|=(2425560213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (230190089/500000000 : ℝ)*x 0 + (748738107/2000000000 : ℝ)*x 1 + (3824076573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230190089/500000000 : ℝ)^89 ≤ (4854999344289/12500000000000 : ℝ)^73 := by
    have hnat : (230190089 : ℕ)^89*12500000000000^73 ≤ 4854999344289^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230190089 500000000 4854999344289 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748738107/2000000000 : ℝ)^89 ≤ (1509199474319/5000000000000 : ℝ)^73 := by
    have hnat : (748738107 : ℕ)^89*5000000000000^73 ≤ 1509199474319^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748738107 2000000000 1509199474319 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3824076573/10000000000 : ℝ)^89 ≤ (30976015746533/100000000000000 : ℝ)^73 := by
    have hnat : (3824076573 : ℕ)^89*100000000000000^73 ≤ 30976015746533^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824076573 10000000000 30976015746533 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(230190089/500000000 : ℝ), (748738107/2000000000 : ℝ), (3824076573/10000000000 : ℝ)] ![(4854999344289/12500000000000 : ℝ), (1509199474319/5000000000000 : ℝ), (30976015746533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(230190089/500000000 : ℝ)|^89 ≤ (4854999344289/12500000000000 : ℝ)^73
        have hw : |(230190089/500000000 : ℝ)|=(230190089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(748738107/2000000000 : ℝ)|^89 ≤ (1509199474319/5000000000000 : ℝ)^73
        have hw : |(748738107/2000000000 : ℝ)|=(748738107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3824076573/10000000000 : ℝ)|^89 ≤ (30976015746533/100000000000000 : ℝ)^73
        have hw : |(3824076573/10000000000 : ℝ)|=(3824076573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (448190641/1000000000 : ℝ)*x 0 + (-3805717053/10000000000 : ℝ)*x 1 + (-3888691803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448190641/1000000000 : ℝ)^89 ≤ (2349368178807/6250000000000 : ℝ)^73 := by
    have hnat : (448190641 : ℕ)^89*6250000000000^73 ≤ 2349368178807^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448190641 1000000000 2349368178807 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3805717053/10000000000 : ℝ)^89 ≤ (6158959777459/20000000000000 : ℝ)^73 := by
    have hnat : (3805717053 : ℕ)^89*20000000000000^73 ≤ 6158959777459^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805717053 10000000000 6158959777459 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3888691803/10000000000 : ℝ)^89 ≤ (15807655118759/50000000000000 : ℝ)^73 := by
    have hnat : (3888691803 : ℕ)^89*50000000000000^73 ≤ 15807655118759^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888691803 10000000000 15807655118759 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448190641/1000000000 : ℝ), (-3805717053/10000000000 : ℝ), (-3888691803/10000000000 : ℝ)] ![(2349368178807/6250000000000 : ℝ), (6158959777459/20000000000000 : ℝ), (15807655118759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448190641/1000000000 : ℝ)|^89 ≤ (2349368178807/6250000000000 : ℝ)^73
        have hw : |(448190641/1000000000 : ℝ)|=(448190641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3805717053/10000000000 : ℝ)|^89 ≤ (6158959777459/20000000000000 : ℝ)^73
        have hw : |(-3805717053/10000000000 : ℝ)|=(3805717053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3888691803/10000000000 : ℝ)|^89 ≤ (15807655118759/50000000000000 : ℝ)^73
        have hw : |(-3888691803/10000000000 : ℝ)|=(3888691803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326039_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3446540283/5000000000 : ℝ)*x 0 + (-118187481/500000000 : ℝ)*x 1 + (2587144633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3446540283/5000000000 : ℝ)^89 ≤ (63532669453201/100000000000000 : ℝ)^73 := by
    have hnat : (3446540283 : ℕ)^89*100000000000000^73 ≤ 63532669453201^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3446540283 5000000000 63532669453201 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118187481/500000000 : ℝ)^89 ≤ (4307731764583/25000000000000 : ℝ)^73 := by
    have hnat : (118187481 : ℕ)^89*25000000000000^73 ≤ 4307731764583^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118187481 500000000 4307731764583 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587144633/10000000000 : ℝ)^89 ≤ (3847280692711/20000000000000 : ℝ)^73 := by
    have hnat : (2587144633 : ℕ)^89*20000000000000^73 ≤ 3847280692711^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587144633 10000000000 3847280692711 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3446540283/5000000000 : ℝ), (-118187481/500000000 : ℝ), (2587144633/10000000000 : ℝ)] ![(63532669453201/100000000000000 : ℝ), (4307731764583/25000000000000 : ℝ), (3847280692711/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3446540283/5000000000 : ℝ)|^89 ≤ (63532669453201/100000000000000 : ℝ)^73
        have hw : |(3446540283/5000000000 : ℝ)|=(3446540283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118187481/500000000 : ℝ)|^89 ≤ (4307731764583/25000000000000 : ℝ)^73
        have hw : |(-118187481/500000000 : ℝ)|=(118187481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587144633/10000000000 : ℝ)|^89 ≤ (3847280692711/20000000000000 : ℝ)^73
        have hw : |(2587144633/10000000000 : ℝ)|=(2587144633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326039 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-35174501/312500000 : ℝ)*X 0 0+(-6146613531/10000000000 : ℝ)*X 0 1+(4500415239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4697435157/10000000000 : ℝ)*X 1 0+(1846540519/5000000000 : ℝ)*X 1 1+(755314969/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-159316259/5000000000 : ℝ)*X 0 0+(-3893388461/5000000000 : ℝ)*X 0 1+(3185411353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1557543761/5000000000 : ℝ)*X 1 0+(426853807/1000000000 : ℝ)*X 1 1+(297522837/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((963938853/2000000000 : ℝ)*X 2 0+(-268379363/1000000000 : ℝ)*X 2 1+(-4601085849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((6535965213/10000000000 : ℝ)*X 0 0+(691771/10000000000 : ℝ)*X 0 1+(297522837/625000000 : ℝ)*X 0 2+(6535965213/10000000000 : ℝ)*X 1 0+(691771/10000000000 : ℝ)*X 1 1+(297522837/625000000 : ℝ)*X 1 2+(6535965213/10000000000 : ℝ)*X 2 0+(691771/10000000000 : ℝ)*X 2 1+(297522837/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-32515541/2500000000 : ℝ)*X 0 0+(-2773107669/5000000000 : ℝ)*X 0 1+(716730561/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((358358231/1000000000 : ℝ)*X 1 0+(2034186441/5000000000 : ℝ)*X 1 1+(2259872529/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((11792499/19531250 : ℝ)*X 2 0+(-2733835119/10000000000 : ℝ)*X 2 1+(-162317921/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2283681053/2500000000 : ℝ)*X 0 0+(-885703/10000000000 : ℝ)*X 0 1+(391966871/2500000000 : ℝ)*X 0 2+(2283681053/2500000000 : ℝ)*X 1 0+(-885703/10000000000 : ℝ)*X 1 1+(391966871/2500000000 : ℝ)*X 1 2+(2283681053/2500000000 : ℝ)*X 2 0+(-885703/10000000000 : ℝ)*X 2 1+(391966871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-694991671/10000000000 : ℝ)*X 0 0+(-1550837053/2000000000 : ℝ)*X 0 1+(2972929873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((612931547/1000000000 : ℝ)*X 1 0+(128521599/400000000 : ℝ)*X 1 1+(1329533763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1241479581/5000000000 : ℝ)*X 2 0+(-5763061189/10000000000 : ℝ)*X 2 1+(-3789060903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((419834393/500000000 : ℝ)*X 0 0+(17/1250000000 : ℝ)*X 0 1+(40341233/156250000 : ℝ)*X 0 2+(419834393/500000000 : ℝ)*X 1 0+(17/1250000000 : ℝ)*X 1 1+(40341233/156250000 : ℝ)*X 1 2+(419834393/500000000 : ℝ)*X 2 0+(17/1250000000 : ℝ)*X 2 1+(40341233/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((23847/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23847/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (83191001455537281/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (58299403333/50000000000 : ℝ)*(base3) + (14309178787/12500000000 : ℝ)*(base7) + (3526831/1000000000000 : ℝ)*(base24) + (3122029/500000000000 : ℝ)*(base40) + (570682887839/1000000000000 : ℝ)*(base49) + (454786269697/250000000000 : ℝ)*(major_s0_0) + (454786269697/250000000000 : ℝ)*(major_s0_1) + (454786269697/250000000000 : ℝ)*(major_s0_2) + (532702413157/250000000000 : ℝ)*(sp_s0_7) + (1648404959663/500000000000 : ℝ)*(sp_s0_8) + (21308005991/10000000000 : ℝ)*(sp_s0_9) + (215172957493/250000000000 : ℝ)*(sp_s0_13) + (6100019/500000000000 : ℝ)*(sp_s0_14) + (3545347/200000000000 : ℝ)*(sp_s0_23) + (110243199209/125000000000 : ℝ)*(f.failure) + (1065410926333/500000000000 : ℝ)*(f.sum) + (2155345572629/25000000000000000000000000 : ℝ)*base63 + (1349387018962891/2500000000000000000000000000 : ℝ)*base65 + (1649144969962891/2500000000000000000000000000 : ℝ)*base66 + (12118114217371/50000000000000000000000000 : ℝ)*base68 + (390158809905659/2500000000000000000000000000 : ℝ)*base70 + (194305047037109/2500000000000000000000000000 : ℝ)*base72 + (20445651207371/50000000000000000000000000 : ℝ)*base74 + (7333759337629/50000000000000000000000000 : ℝ)*base77 + (2401348581/10000000000000000000000 : ℝ)*base79 + (1123/2500000000000000 : ℝ)*base86 + (1123/2500000000000000 : ℝ)*base88 + (1123/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9819/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-9819/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3063578038221327738873/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304205427731/500000000000 : ℝ)*(base7) + (458393/500000000000 : ℝ)*(base13) + (1006303793859/1000000000000 : ℝ)*(base40) + (923809/250000000000 : ℝ)*(base53) + (2908644199101/1000000000000 : ℝ)*(major_s0_0) + (2908644199101/1000000000000 : ℝ)*(major_s0_1) + (581728100773/200000000000 : ℝ)*(major_s0_2) + (20624479/1000000000000 : ℝ)*(sp_s0_0) + (95677/20000000000 : ℝ)*(sp_s0_1) + (2037329510079/500000000000 : ℝ)*(sp_s0_14) + (1018668944393/250000000000 : ℝ)*(sp_s0_15) + (4074684256659/1000000000000 : ℝ)*(sp_s0_16) + (252318405331/125000000000 : ℝ)*(sp_s0_20) + (12789407/1000000000000 : ℝ)*(sp_s0_27) + (705074588297/500000000000 : ℝ)*(f.failure) + (4074684256659/1000000000000 : ℝ)*(f.sum) + (70742096130631/100000000000000000000000000 : ℝ)*base63 + (496918738586519/2000000000000000000000000000 : ℝ)*base65 + (980789575187297/10000000000000000000000000000 : ℝ)*base67 + (31539776579161/40000000000000000000000000 : ℝ)*base69 + (386004918841089/2000000000000000000000000000 : ℝ)*base71 + (7452967781812703/10000000000000000000000000000 : ℝ)*base73 + (105543109405457/200000000000000000000000000 : ℝ)*base75 + (17983761425457/200000000000000000000000000 : ℝ)*base77 + (518613991/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (6141/10000000000000000 : ℝ)*base87 + (6141/10000000000000000 : ℝ)*base89 + (6141/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61783/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61783/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4131875660847632713113/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51051526847/250000000000 : ℝ)*(base3) + (79085540629/62500000000 : ℝ)*(base7) + (379778026647/1000000000000 : ℝ)*(base40) + (512851/125000000000 : ℝ)*(base43) + (2454073/1000000000000 : ℝ)*(base49) + (127486156179/62500000000 : ℝ)*(major_s0_0) + (254971799507/125000000000 : ℝ)*(major_s0_1) + (127486156179/62500000000 : ℝ)*(major_s0_2) + (2080303/500000000000 : ℝ)*(sp_s0_16) + (35182483/1000000000000 : ℝ)*(sp_s0_20) + (2399203706037/1000000000000 : ℝ)*(sp_s0_21) + (2603413916233/1000000000000 : ℝ)*(sp_s0_22) + (2399199545431/1000000000000 : ℝ)*(sp_s0_23) + (2050038953951/1000000000000 : ℝ)*(sp_s0_27) + (494455796879/500000000000 : ℝ)*(f.failure) + (479841561769/200000000000 : ℝ)*(f.sum) + (2263198620139/5000000000000000000000000 : ℝ)*base62 + (27293026490137/625000000000000000000000000 : ℝ)*base65 + (9110925648679/1250000000000000000000000000 : ℝ)*base67 + (6786115545997/12500000000000000000000000 : ℝ)*base68 + (90589076684713/625000000000000000000000000 : ℝ)*base70 + (13614577259863/625000000000000000000000000 : ℝ)*base72 + (16510197366201/25000000000000000000000000 : ℝ)*base74 + (2360314855997/12500000000000000000000000 : ℝ)*base76 + (635269728128953/1250000000000000000000000000 : ℝ)*base79 + (9387/10000000000000000 : ℝ)*base87 + (9387/10000000000000000 : ℝ)*base89 + (9387/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (23847/50000 : ℝ) ^ (87/16 : ℝ) ≤ (1785034549388168737/100000000000000000000 : ℝ) := by
    have hpowers : (23847/50000 : ℝ)^87 ≤ (1785034549388168737/100000000000000000000 : ℝ)^16 := by
      have hnat : (23847 : ℕ)^87*100000000000000000000^16 ≤ 1785034549388168737^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23847 50000 1785034549388168737 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23847/50000 : ℝ)) (X := (1785034549388168737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (101785034549388168737/100000000000000000000 : ℝ) ≤ (1254073957558087/1250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (101785034549388168737/100000000000000000000 : ℝ)^16 ≤ (1254073957558087/1250000000000000 : ℝ)^87 := by
      have hnat : (101785034549388168737 : ℕ)^16*1250000000000000^87 ≤ 1254073957558087^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101785034549388168737 100000000000000000000 1254073957558087 1250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254073957558087/1250000000000000 : ℝ)) (X := (101785034549388168737/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (51785034549388168737/50000000000000000000 : ℝ) ≤ (2012944031280169/2000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (51785034549388168737/50000000000000000000 : ℝ)^16 ≤ (2012944031280169/2000000000000000 : ℝ)^87 := by
      have hnat : (51785034549388168737 : ℕ)^16*2000000000000000^87 ≤ 2012944031280169^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51785034549388168737 50000000000000000000 2012944031280169 2000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012944031280169/2000000000000000 : ℝ)) (X := (51785034549388168737/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4073957558087/596175000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10709498645383/1589800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (23847/50000 : ℝ)) (alpha := (4073957558087/596175000000000 : ℝ)) (beta := (10709498645383/1589800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (23847/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4073957558087/596175000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10709498645383/1589800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9819/25000 : ℝ) ^ (87/16 : ℝ) ≤ (620964723906859143/100000000000000000000 : ℝ) := by
    have hpowers : (9819/25000 : ℝ)^87 ≤ (620964723906859143/100000000000000000000 : ℝ)^16 := by
      have hnat : (9819 : ℕ)^87*100000000000000000000^16 ≤ 620964723906859143^16*25000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9819 25000 620964723906859143 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9819/25000 : ℝ)) (X := (620964723906859143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100620964723906859143/100000000000000000000 : ℝ) ≤ (5005695606427329/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (100620964723906859143/100000000000000000000 : ℝ)^16 ≤ (5005695606427329/5000000000000000 : ℝ)^87 := by
      have hnat : (100620964723906859143 : ℕ)^16*5000000000000000^87 ≤ 5005695606427329^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100620964723906859143 100000000000000000000 5005695606427329 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005695606427329/5000000000000000 : ℝ)) (X := (100620964723906859143/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50620964723906859143/50000000000000000000 : ℝ) ≤ (5011362599536949/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50620964723906859143/50000000000000000000 : ℝ)^16 ≤ (5011362599536949/5000000000000000 : ℝ)^87 := by
      have hnat : (50620964723906859143 : ℕ)^16*5000000000000000^87 ≤ 5011362599536949^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50620964723906859143 50000000000000000000 5011362599536949 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011362599536949/5000000000000000 : ℝ)) (X := (50620964723906859143/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5695606427329/1963800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(283349655481/98190000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (9819/25000 : ℝ)) (alpha := (5695606427329/1963800000000000 : ℝ)) (beta := (283349655481/98190000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9819/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5695606427329/1963800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(283349655481/98190000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (61783/100000 : ℝ) ^ (87/16 : ℝ) ≤ (227876829602300709/3125000000000000000 : ℝ) := by
    have hpowers : (61783/100000 : ℝ)^87 ≤ (227876829602300709/3125000000000000000 : ℝ)^16 := by
      have hnat : (61783 : ℕ)^87*3125000000000000000^16 ≤ 227876829602300709^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61783 100000 227876829602300709 3125000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61783/100000 : ℝ)) (X := (227876829602300709/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3352876829602300709/3125000000000000000 : ℝ) ≤ (5065142030969973/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3352876829602300709/3125000000000000000 : ℝ)^16 ≤ (5065142030969973/5000000000000000 : ℝ)^87 := by
      have hnat : (3352876829602300709 : ℕ)^16*5000000000000000^87 ≤ 5065142030969973^87*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3352876829602300709 3125000000000000000 5065142030969973 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5065142030969973/5000000000000000 : ℝ)) (X := (3352876829602300709/3125000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1790376829602300709/1562500000000000000 : ℝ) ≤ (10253531195293029/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (1790376829602300709/1562500000000000000 : ℝ)^16 ≤ (10253531195293029/10000000000000000 : ℝ)^87 := by
      have hnat : (1790376829602300709 : ℕ)^16*10000000000000000^87 ≤ 10253531195293029^87*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1790376829602300709 1562500000000000000 10253531195293029 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10253531195293029/10000000000000000 : ℝ)) (X := (1790376829602300709/1562500000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(65142030969973/3089150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(123247133353083/6178300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (61783/100000 : ℝ)) (alpha := (65142030969973/3089150000000000 : ℝ)) (beta := (123247133353083/6178300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61783/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(65142030969973/3089150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(123247133353083/6178300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2079031663/10000000000 : ℝ)*X 0 0+(-1271767241/2500000000 : ℝ)*X 0 1+(2425560213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((230190089/500000000 : ℝ)*X 1 0+(748738107/2000000000 : ℝ)*X 1 1+(3824076573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((448190641/1000000000 : ℝ)*X 2 0+(-3805717053/10000000000 : ℝ)*X 2 1+(-3888691803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3446540283/5000000000 : ℝ)*X 0 0+(-118187481/500000000 : ℝ)*X 0 1+(2587144633/10000000000 : ℝ)*X 0 2+(3446540283/5000000000 : ℝ)*X 1 0+(-118187481/500000000 : ℝ)*X 1 1+(2587144633/10000000000 : ℝ)*X 1 2+(3446540283/5000000000 : ℝ)*X 2 0+(-118187481/500000000 : ℝ)*X 2 1+(2587144633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326039_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-24734381619632819440704073725442909/2679021780485000000000000000000000 : ℝ) := by norm_num
    linear_combination (611391/1000000000000 : ℝ)*(base10) + (38567/1000000000000 : ℝ)*(base17) + (50423/200000000000 : ℝ)*(base19) + (53707/1000000000000 : ℝ)*(base21) + (40059733291/62500000000 : ℝ)*(base40) + (305032380481/1000000000000 : ℝ)*(base49) + (109781464673/500000000000 : ℝ)*(base59) + (60699/1000000000000 : ℝ)*(ratio_s0_1) + (41253/20000 : ℝ)*(major_s1_0) + (41253/20000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (384692292133/125000000000 : ℝ)*(sp_s1_0) + (1538769328887/500000000000 : ℝ)*(sp_s1_1) + (3077538894749/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (384692368557/125000000000 : ℝ)*(f.sum) + (7606947408696361/252769698750000000000000000000 : ℝ)*base63 + (2965837974251/19307187500000000000000000 : ℝ)*base64 + (693451856183/2045625000000000000000000 : ℝ)*base67 + (1990613588631/15445750000000000000000000 : ℝ)*base69 + (94901452540390097/491113067000000000000000000000 : ℝ)*base71 + (6851638181199/39745000000000000000000000 : ℝ)*base72 + (661398018757/3273000000000000000000000 : ℝ)*base74 + (10321075786453/79490000000000000000000000 : ℝ)*base77 + (11527318396367419/260170770000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c326040_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2897922679/10000000000 : ℝ)*x 0 + (-2307499531/5000000000 : ℝ)*x 1 + (-4614999021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2897922679/10000000000 : ℝ)^89 ≤ (11044803992469/50000000000000 : ℝ)^73 := by
    have hnat : (2897922679 : ℕ)^89*50000000000000^73 ≤ 11044803992469^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897922679 10000000000 11044803992469 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307499531/5000000000 : ℝ)^89 ≤ (38955196212677/100000000000000 : ℝ)^73 := by
    have hnat : (2307499531 : ℕ)^89*100000000000000^73 ≤ 38955196212677^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307499531 5000000000 38955196212677 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4614999021/10000000000 : ℝ)^89 ≤ (19477597895371/50000000000000 : ℝ)^73 := by
    have hnat : (4614999021 : ℕ)^89*50000000000000^73 ≤ 19477597895371^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4614999021 10000000000 19477597895371 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2897922679/10000000000 : ℝ), (-2307499531/5000000000 : ℝ), (-4614999021/10000000000 : ℝ)] ![(11044803992469/50000000000000 : ℝ), (38955196212677/100000000000000 : ℝ), (19477597895371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2897922679/10000000000 : ℝ)|^89 ≤ (11044803992469/50000000000000 : ℝ)^73
        have hw : |(-2897922679/10000000000 : ℝ)|=(2897922679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2307499531/5000000000 : ℝ)|^89 ≤ (38955196212677/100000000000000 : ℝ)^73
        have hw : |(-2307499531/5000000000 : ℝ)|=(2307499531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4614999021/10000000000 : ℝ)|^89 ≤ (19477597895371/50000000000000 : ℝ)^73
        have hw : |(-4614999021/10000000000 : ℝ)|=(4614999021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326040_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2897922679/10000000000 : ℝ)*x 0 + (2307499531/5000000000 : ℝ)*x 1 + (-4614999021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2897922679/10000000000 : ℝ)^89 ≤ (11044803992469/50000000000000 : ℝ)^73 := by
    have hnat : (2897922679 : ℕ)^89*50000000000000^73 ≤ 11044803992469^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897922679 10000000000 11044803992469 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307499531/5000000000 : ℝ)^89 ≤ (38955196212677/100000000000000 : ℝ)^73 := by
    have hnat : (2307499531 : ℕ)^89*100000000000000^73 ≤ 38955196212677^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307499531 5000000000 38955196212677 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4614999021/10000000000 : ℝ)^89 ≤ (19477597895371/50000000000000 : ℝ)^73 := by
    have hnat : (4614999021 : ℕ)^89*50000000000000^73 ≤ 19477597895371^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4614999021 10000000000 19477597895371 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2897922679/10000000000 : ℝ), (2307499531/5000000000 : ℝ), (-4614999021/10000000000 : ℝ)] ![(11044803992469/50000000000000 : ℝ), (38955196212677/100000000000000 : ℝ), (19477597895371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2897922679/10000000000 : ℝ)|^89 ≤ (11044803992469/50000000000000 : ℝ)^73
        have hw : |(2897922679/10000000000 : ℝ)|=(2897922679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2307499531/5000000000 : ℝ)|^89 ≤ (38955196212677/100000000000000 : ℝ)^73
        have hw : |(2307499531/5000000000 : ℝ)|=(2307499531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4614999021/10000000000 : ℝ)|^89 ≤ (19477597895371/50000000000000 : ℝ)^73
        have hw : |(-4614999021/10000000000 : ℝ)|=(4614999021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326040_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (114998049/200000000 : ℝ)*x 0 + (-315848803/1000000000 : ℝ)*x 1 + (3158488001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114998049/200000000 : ℝ)^89 ≤ (12732782765119/25000000000000 : ℝ)^73 := by
    have hnat : (114998049 : ℕ)^89*25000000000000^73 ≤ 12732782765119^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114998049 200000000 12732782765119 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315848803/1000000000 : ℝ)^89 ≤ (24534434600583/100000000000000 : ℝ)^73 := by
    have hnat : (315848803 : ℕ)^89*100000000000000^73 ≤ 24534434600583^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315848803 1000000000 24534434600583 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3158488001/10000000000 : ℝ)^89 ≤ (3066804290743/12500000000000 : ℝ)^73 := by
    have hnat : (3158488001 : ℕ)^89*12500000000000^73 ≤ 3066804290743^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158488001 10000000000 3066804290743 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114998049/200000000 : ℝ), (-315848803/1000000000 : ℝ), (3158488001/10000000000 : ℝ)] ![(12732782765119/25000000000000 : ℝ), (24534434600583/100000000000000 : ℝ), (3066804290743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114998049/200000000 : ℝ)|^89 ≤ (12732782765119/25000000000000 : ℝ)^73
        have hw : |(114998049/200000000 : ℝ)|=(114998049/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-315848803/1000000000 : ℝ)|^89 ≤ (24534434600583/100000000000000 : ℝ)^73
        have hw : |(-315848803/1000000000 : ℝ)|=(315848803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3158488001/10000000000 : ℝ)|^89 ≤ (3066804290743/12500000000000 : ℝ)^73
        have hw : |(3158488001/10000000000 : ℝ)|=(3158488001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326040_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (114998049/200000000 : ℝ)*x 0 + (-315848803/1000000000 : ℝ)*x 1 + (-3158488001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114998049/200000000 : ℝ)^89 ≤ (12732782765119/25000000000000 : ℝ)^73 := by
    have hnat : (114998049 : ℕ)^89*25000000000000^73 ≤ 12732782765119^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114998049 200000000 12732782765119 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315848803/1000000000 : ℝ)^89 ≤ (24534434600583/100000000000000 : ℝ)^73 := by
    have hnat : (315848803 : ℕ)^89*100000000000000^73 ≤ 24534434600583^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315848803 1000000000 24534434600583 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3158488001/10000000000 : ℝ)^89 ≤ (3066804290743/12500000000000 : ℝ)^73 := by
    have hnat : (3158488001 : ℕ)^89*12500000000000^73 ≤ 3066804290743^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158488001 10000000000 3066804290743 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114998049/200000000 : ℝ), (-315848803/1000000000 : ℝ), (-3158488001/10000000000 : ℝ)] ![(12732782765119/25000000000000 : ℝ), (24534434600583/100000000000000 : ℝ), (3066804290743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114998049/200000000 : ℝ)|^89 ≤ (12732782765119/25000000000000 : ℝ)^73
        have hw : |(114998049/200000000 : ℝ)|=(114998049/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-315848803/1000000000 : ℝ)|^89 ≤ (24534434600583/100000000000000 : ℝ)^73
        have hw : |(-315848803/1000000000 : ℝ)|=(315848803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3158488001/10000000000 : ℝ)|^89 ≤ (3066804290743/12500000000000 : ℝ)^73
        have hw : |(-3158488001/10000000000 : ℝ)|=(3158488001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326040 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2897922679/10000000000 : ℝ)*X 0 0+(-2307499531/5000000000 : ℝ)*X 0 1+(-4614999021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326040_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2897922679/10000000000 : ℝ)*X 1 0+(2307499531/5000000000 : ℝ)*X 1 1+(-4614999021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326040_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((114998049/200000000 : ℝ)*X 2 0+(-315848803/1000000000 : ℝ)*X 2 1+(3158488001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326040_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((114998049/200000000 : ℝ)*X 0 0+(-315848803/1000000000 : ℝ)*X 0 1+(-3158488001/10000000000 : ℝ)*X 0 2+(114998049/200000000 : ℝ)*X 1 0+(-315848803/1000000000 : ℝ)*X 1 1+(-3158488001/10000000000 : ℝ)*X 1 2+(114998049/200000000 : ℝ)*X 2 0+(-315848803/1000000000 : ℝ)*X 2 1+(-3158488001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326040_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-461248999159086354619425939/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372329238651/500000000000 : ℝ)*(base5) + (1157/100000000000 : ℝ)*(base15) + (1123/125000000000 : ℝ)*(base33) + (876629548241/1000000000000 : ℝ)*(base39) + (247568411783/500000000000 : ℝ)*(base40) + (381492714399/1000000000000 : ℝ)*(base49) + (4629/250000000000 : ℝ)*(base53) + (29771616107/40000000000 : ℝ)*(base60) + (257831248877/125000000000 : ℝ)*(major_s0_0) + (41253/20000 : ℝ)*(major_s0_1) + (515662495371/250000000000 : ℝ)*(major_s0_2) + (1537496654603/500000000000 : ℝ)*(sp_s0_0) + (3074993288653/1000000000000 : ℝ)*(sp_s0_1) + (3819651796041/1000000000000 : ℝ)*(sp_s0_2) + (127670761349/500000000000 : ℝ)*(sp_s0_6) + (1537496663861/500000000000 : ℝ)*(f.sum) + (14309357491847/50000000000000000000000000 : ℝ)*base62 + (123346519459513/2500000000000000000000000000 : ℝ)*base64 + (2088784013/5000000000000000000000 : ℝ)*base66 + (50885591296847/50000000000000000000000000 : ℝ)*base68 + (261881349770613/2500000000000000000000000000 : ℝ)*base70 + (351058868447431/1250000000000000000000000000 : ℝ)*base73 + (106814161/200000000000000000000 : ℝ)*base74 + (3979342233111/25000000000000000000000000 : ℝ)*base76 + (490657017947431/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b018 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=39 ∨ c=40 := by omega
  rcases hc with rfl|rfl
  · exact collision_c326039 p hpa (by linarith only [hpb]) X hX
  · exact collision_c326040 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
