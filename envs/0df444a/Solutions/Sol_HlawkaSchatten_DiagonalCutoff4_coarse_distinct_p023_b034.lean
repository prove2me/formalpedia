-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:51:13.471989+00:00
-- url     : https://prove2.me/submissions/3393a1ab-298e-4f54-a703-d1656e9103d2

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
theorem collision_support_c323059_s0_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-117842759/400000000 : ℝ)*x 0 + (2946068669/10000000000 : ℝ)*x 1 + (623613883/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117842759/400000000 : ℝ)^21 ≤ (22098301241239/100000000000000 : ℝ)^17 := by
    have hnat : (117842759 : ℕ)^21*100000000000000^17 ≤ 22098301241239^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117842759 400000000 22098301241239 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2946068669/10000000000 : ℝ)^21 ≤ (22098298405881/100000000000000 : ℝ)^17 := by
    have hnat : (2946068669 : ℕ)^21*100000000000000^17 ≤ 22098298405881^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946068669 10000000000 22098298405881 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623613883/1000000000 : ℝ)^21 ≤ (27901700171579/50000000000000 : ℝ)^17 := by
    have hnat : (623613883 : ℕ)^21*50000000000000^17 ≤ 27901700171579^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623613883 1000000000 27901700171579 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117842759/400000000 : ℝ), (2946068669/10000000000 : ℝ), (623613883/1000000000 : ℝ)] ![(22098301241239/100000000000000 : ℝ), (22098298405881/100000000000000 : ℝ), (27901700171579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117842759/400000000 : ℝ)|^21 ≤ (22098301241239/100000000000000 : ℝ)^17
        have hw : |(-117842759/400000000 : ℝ)|=(117842759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2946068669/10000000000 : ℝ)|^21 ≤ (22098298405881/100000000000000 : ℝ)^17
        have hw : |(2946068669/10000000000 : ℝ)|=(2946068669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(623613883/1000000000 : ℝ)|^21 ≤ (27901700171579/50000000000000 : ℝ)^17
        have hw : |(623613883/1000000000 : ℝ)|=(623613883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1473034577/5000000000 : ℝ)*x 0 + (-294606873/1000000000 : ℝ)*x 1 + (1559034657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1473034577/5000000000 : ℝ)^21 ≤ (2209830289983/10000000000000 : ℝ)^17 := by
    have hnat : (1473034577 : ℕ)^21*10000000000000^17 ≤ 2209830289983^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473034577 5000000000 2209830289983 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294606873/1000000000 : ℝ)^21 ≤ (220982989711/1000000000000 : ℝ)^17 := by
    have hnat : (294606873 : ℕ)^21*1000000000000^17 ≤ 220982989711^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294606873 1000000000 220982989711 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1559034657/2500000000 : ℝ)^21 ≤ (871928095473/1562500000000 : ℝ)^17 := by
    have hnat : (1559034657 : ℕ)^21*1562500000000^17 ≤ 871928095473^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559034657 2500000000 871928095473 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1473034577/5000000000 : ℝ), (-294606873/1000000000 : ℝ), (1559034657/2500000000 : ℝ)] ![(2209830289983/10000000000000 : ℝ), (220982989711/1000000000000 : ℝ), (871928095473/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1473034577/5000000000 : ℝ)|^21 ≤ (2209830289983/10000000000000 : ℝ)^17
        have hw : |(1473034577/5000000000 : ℝ)|=(1473034577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294606873/1000000000 : ℝ)|^21 ≤ (220982989711/1000000000000 : ℝ)^17
        have hw : |(-294606873/1000000000 : ℝ)|=(294606873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1559034657/2500000000 : ℝ)|^21 ≤ (871928095473/1562500000000 : ℝ)^17
        have hw : |(1559034657/2500000000 : ℝ)|=(1559034657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1460334443/5000000000 : ℝ)*x 0 + (1283279769/2000000000 : ℝ)*x 1 + (2754176877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1460334443/5000000000 : ℝ)^21 ≤ (10931593243789/50000000000000 : ℝ)^17 := by
    have hnat : (1460334443 : ℕ)^21*50000000000000^17 ≤ 10931593243789^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460334443 5000000000 10931593243789 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283279769/2000000000 : ℝ)^21 ≤ (11560540415571/20000000000000 : ℝ)^17 := by
    have hnat : (1283279769 : ℕ)^21*20000000000000^17 ≤ 11560540415571^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283279769 2000000000 11560540415571 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754176877/10000000000 : ℝ)^21 ≤ (20334111425653/100000000000000 : ℝ)^17 := by
    have hnat : (2754176877 : ℕ)^21*100000000000000^17 ≤ 20334111425653^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754176877 10000000000 20334111425653 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1460334443/5000000000 : ℝ), (1283279769/2000000000 : ℝ), (2754176877/10000000000 : ℝ)] ![(10931593243789/50000000000000 : ℝ), (11560540415571/20000000000000 : ℝ), (20334111425653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1460334443/5000000000 : ℝ)|^21 ≤ (10931593243789/50000000000000 : ℝ)^17
        have hw : |(1460334443/5000000000 : ℝ)|=(1460334443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283279769/2000000000 : ℝ)|^21 ≤ (11560540415571/20000000000000 : ℝ)^17
        have hw : |(1283279769/2000000000 : ℝ)|=(1283279769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754176877/10000000000 : ℝ)|^21 ≤ (20334111425653/100000000000000 : ℝ)^17
        have hw : |(2754176877/10000000000 : ℝ)|=(2754176877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2226707161/10000000000 : ℝ)*x 0 + (138155927/2500000000 : ℝ)*x 1 + (8479420311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2226707161/10000000000 : ℝ)^21 ≤ (7818835501301/50000000000000 : ℝ)^17 := by
    have hnat : (2226707161 : ℕ)^21*50000000000000^17 ≤ 7818835501301^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226707161 10000000000 7818835501301 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138155927/2500000000 : ℝ)^21 ≤ (698989389031/25000000000000 : ℝ)^17 := by
    have hnat : (138155927 : ℕ)^21*25000000000000^17 ≤ 698989389031^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138155927 2500000000 698989389031 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8479420311/10000000000 : ℝ)^21 ≤ (4078318570963/5000000000000 : ℝ)^17 := by
    have hnat : (8479420311 : ℕ)^21*5000000000000^17 ≤ 4078318570963^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8479420311 10000000000 4078318570963 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2226707161/10000000000 : ℝ), (138155927/2500000000 : ℝ), (8479420311/10000000000 : ℝ)] ![(7818835501301/50000000000000 : ℝ), (698989389031/25000000000000 : ℝ), (4078318570963/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2226707161/10000000000 : ℝ)|^21 ≤ (7818835501301/50000000000000 : ℝ)^17
        have hw : |(-2226707161/10000000000 : ℝ)|=(2226707161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138155927/2500000000 : ℝ)|^21 ≤ (698989389031/25000000000000 : ℝ)^17
        have hw : |(138155927/2500000000 : ℝ)|=(138155927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8479420311/10000000000 : ℝ)|^21 ≤ (4078318570963/5000000000000 : ℝ)^17
        have hw : |(8479420311/10000000000 : ℝ)|=(8479420311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (153444497/1000000000 : ℝ)*x 0 + (-42729171/312500000 : ℝ)*x 1 + (8479419449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153444497/1000000000 : ℝ)^21 ≤ (9872120585213/100000000000000 : ℝ)^17 := by
    have hnat : (153444497 : ℕ)^21*100000000000000^17 ≤ 9872120585213^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153444497 1000000000 9872120585213 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42729171/312500000 : ℝ)^21 ≤ (2140379555937/25000000000000 : ℝ)^17 := by
    have hnat : (42729171 : ℕ)^21*25000000000000^17 ≤ 2140379555937^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42729171 312500000 2140379555937 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8479419449/10000000000 : ℝ)^21 ≤ (81566361176367/100000000000000 : ℝ)^17 := by
    have hnat : (8479419449 : ℕ)^21*100000000000000^17 ≤ 81566361176367^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8479419449 10000000000 81566361176367 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(153444497/1000000000 : ℝ), (-42729171/312500000 : ℝ), (8479419449/10000000000 : ℝ)] ![(9872120585213/100000000000000 : ℝ), (2140379555937/25000000000000 : ℝ), (81566361176367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(153444497/1000000000 : ℝ)|^21 ≤ (9872120585213/100000000000000 : ℝ)^17
        have hw : |(153444497/1000000000 : ℝ)|=(153444497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42729171/312500000 : ℝ)|^21 ≤ (2140379555937/25000000000000 : ℝ)^17
        have hw : |(-42729171/312500000 : ℝ)|=(42729171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8479419449/10000000000 : ℝ)|^21 ≤ (81566361176367/100000000000000 : ℝ)^17
        have hw : |(8479419449/10000000000 : ℝ)|=(8479419449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (420800027/1000000000 : ℝ)*x 0 + (3557343279/5000000000 : ℝ)*x 1 + (-520481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420800027/1000000000 : ℝ)^21 ≤ (3432598405609/10000000000000 : ℝ)^17 := by
    have hnat : (420800027 : ℕ)^21*10000000000000^17 ≤ 3432598405609^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420800027 1000000000 3432598405609 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3557343279/5000000000 : ℝ)^21 ≤ (16417571001009/25000000000000 : ℝ)^17 := by
    have hnat : (3557343279 : ℕ)^21*25000000000000^17 ≤ 16417571001009^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3557343279 5000000000 16417571001009 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520481/2000000000 : ℝ)^21 ≤ (74638633/2000000000000 : ℝ)^17 := by
    have hnat : (520481 : ℕ)^21*2000000000000^17 ≤ 74638633^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520481 2000000000 74638633 2000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420800027/1000000000 : ℝ), (3557343279/5000000000 : ℝ), (-520481/2000000000 : ℝ)] ![(3432598405609/10000000000000 : ℝ), (16417571001009/25000000000000 : ℝ), (74638633/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420800027/1000000000 : ℝ)|^21 ≤ (3432598405609/10000000000000 : ℝ)^17
        have hw : |(420800027/1000000000 : ℝ)|=(420800027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3557343279/5000000000 : ℝ)|^21 ≤ (16417571001009/25000000000000 : ℝ)^17
        have hw : |(3557343279/5000000000 : ℝ)|=(3557343279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520481/2000000000 : ℝ)|^21 ≤ (74638633/2000000000000 : ℝ)^17
        have hw : |(-520481/2000000000 : ℝ)|=(520481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1882197843/10000000000 : ℝ)*x 0 + (4085744659/5000000000 : ℝ)*x 1 + (147110669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882197843/10000000000 : ℝ)^21 ≤ (2541138125353/20000000000000 : ℝ)^17 := by
    have hnat : (1882197843 : ℕ)^21*20000000000000^17 ≤ 2541138125353^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882197843 10000000000 2541138125353 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4085744659/5000000000 : ℝ)^21 ≤ (4870193615007/6250000000000 : ℝ)^17 := by
    have hnat : (4085744659 : ℕ)^21*6250000000000^17 ≤ 4870193615007^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085744659 5000000000 4870193615007 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147110669/1000000000 : ℝ)^21 ≤ (1171401438509/12500000000000 : ℝ)^17 := by
    have hnat : (147110669 : ℕ)^21*12500000000000^17 ≤ 1171401438509^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147110669 1000000000 1171401438509 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1882197843/10000000000 : ℝ), (4085744659/5000000000 : ℝ), (147110669/1000000000 : ℝ)] ![(2541138125353/20000000000000 : ℝ), (4870193615007/6250000000000 : ℝ), (1171401438509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1882197843/10000000000 : ℝ)|^21 ≤ (2541138125353/20000000000000 : ℝ)^17
        have hw : |(1882197843/10000000000 : ℝ)|=(1882197843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4085744659/5000000000 : ℝ)|^21 ≤ (4870193615007/6250000000000 : ℝ)^17
        have hw : |(4085744659/5000000000 : ℝ)|=(4085744659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147110669/1000000000 : ℝ)|^21 ≤ (1171401438509/12500000000000 : ℝ)^17
        have hw : |(147110669/1000000000 : ℝ)|=(147110669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-966521069/10000000000 : ℝ)*x 0 + (1827201891/10000000000 : ℝ)*x 1 + (8530506863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966521069/10000000000 : ℝ)^21 ≤ (174296048601/3125000000000 : ℝ)^17 := by
    have hnat : (966521069 : ℕ)^21*3125000000000^17 ≤ 174296048601^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966521069 10000000000 174296048601 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827201891/10000000000 : ℝ)^21 ≤ (12248678918391/100000000000000 : ℝ)^17 := by
    have hnat : (1827201891 : ℕ)^21*100000000000000^17 ≤ 12248678918391^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827201891 10000000000 12248678918391 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8530506863/10000000000 : ℝ)^21 ≤ (410869237559/500000000000 : ℝ)^17 := by
    have hnat : (8530506863 : ℕ)^21*500000000000^17 ≤ 410869237559^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8530506863 10000000000 410869237559 500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966521069/10000000000 : ℝ), (1827201891/10000000000 : ℝ), (8530506863/10000000000 : ℝ)] ![(174296048601/3125000000000 : ℝ), (12248678918391/100000000000000 : ℝ), (410869237559/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966521069/10000000000 : ℝ)|^21 ≤ (174296048601/3125000000000 : ℝ)^17
        have hw : |(-966521069/10000000000 : ℝ)|=(966521069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1827201891/10000000000 : ℝ)|^21 ≤ (12248678918391/100000000000000 : ℝ)^17
        have hw : |(1827201891/10000000000 : ℝ)|=(1827201891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8530506863/10000000000 : ℝ)|^21 ≤ (410869237559/500000000000 : ℝ)^17
        have hw : |(8530506863/10000000000 : ℝ)|=(8530506863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (217282833/2500000000 : ℝ)*x 0 + (-1909589929/10000000000 : ℝ)*x 1 + (4265252197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217282833/2500000000 : ℝ)^21 ≤ (978336910703/20000000000000 : ℝ)^17 := by
    have hnat : (217282833 : ℕ)^21*20000000000000^17 ≤ 978336910703^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217282833 2500000000 978336910703 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909589929/10000000000 : ℝ)^21 ≤ (6467248650523/50000000000000 : ℝ)^17 := by
    have hnat : (1909589929 : ℕ)^21*50000000000000^17 ≤ 6467248650523^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909589929 10000000000 6467248650523 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4265252197/5000000000 : ℝ)^21 ≤ (16434763626381/20000000000000 : ℝ)^17 := by
    have hnat : (4265252197 : ℕ)^21*20000000000000^17 ≤ 16434763626381^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265252197 5000000000 16434763626381 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217282833/2500000000 : ℝ), (-1909589929/10000000000 : ℝ), (4265252197/5000000000 : ℝ)] ![(978336910703/20000000000000 : ℝ), (6467248650523/50000000000000 : ℝ), (16434763626381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217282833/2500000000 : ℝ)|^21 ≤ (978336910703/20000000000000 : ℝ)^17
        have hw : |(217282833/2500000000 : ℝ)|=(217282833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909589929/10000000000 : ℝ)|^21 ≤ (6467248650523/50000000000000 : ℝ)^17
        have hw : |(-1909589929/10000000000 : ℝ)|=(1909589929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4265252197/5000000000 : ℝ)|^21 ≤ (16434763626381/20000000000000 : ℝ)^17
        have hw : |(4265252197/5000000000 : ℝ)|=(4265252197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (847658059/1000000000 : ℝ)*x 0 + (636897177/2500000000 : ℝ)*x 1 + (-449673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847658059/1000000000 : ℝ)^21 ≤ (81532629179019/100000000000000 : ℝ)^17 := by
    have hnat : (847658059 : ℕ)^21*100000000000000^17 ≤ 81532629179019^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847658059 1000000000 81532629179019 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636897177/2500000000 : ℝ)^21 ≤ (18466944180973/100000000000000 : ℝ)^17 := by
    have hnat : (636897177 : ℕ)^21*100000000000000^17 ≤ 18466944180973^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636897177 2500000000 18466944180973 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449673/10000000000 : ℝ)^21 ≤ (213313827/50000000000000 : ℝ)^17 := by
    have hnat : (449673 : ℕ)^21*50000000000000^17 ≤ 213313827^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449673 10000000000 213313827 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847658059/1000000000 : ℝ), (636897177/2500000000 : ℝ), (-449673/10000000000 : ℝ)] ![(81532629179019/100000000000000 : ℝ), (18466944180973/100000000000000 : ℝ), (213313827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847658059/1000000000 : ℝ)|^21 ≤ (81532629179019/100000000000000 : ℝ)^17
        have hw : |(847658059/1000000000 : ℝ)|=(847658059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636897177/2500000000 : ℝ)|^21 ≤ (18466944180973/100000000000000 : ℝ)^17
        have hw : |(636897177/2500000000 : ℝ)|=(636897177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449673/10000000000 : ℝ)|^21 ≤ (213313827/50000000000000 : ℝ)^17
        have hw : |(-449673/10000000000 : ℝ)|=(449673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3344456423/5000000000 : ℝ)*x 0 + (3422411199/10000000000 : ℝ)*x 1 + (4660851/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3344456423/5000000000 : ℝ)^21 ≤ (30425149918937/50000000000000 : ℝ)^17 := by
    have hnat : (3344456423 : ℕ)^21*50000000000000^17 ≤ 30425149918937^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3344456423 5000000000 30425149918937 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3422411199/10000000000 : ℝ)^21 ≤ (26592752494171/100000000000000 : ℝ)^17 := by
    have hnat : (3422411199 : ℕ)^21*100000000000000^17 ≤ 26592752494171^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422411199 10000000000 26592752494171 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4660851/25000000 : ℝ)^21 ≤ (6278473828221/50000000000000 : ℝ)^17 := by
    have hnat : (4660851 : ℕ)^21*50000000000000^17 ≤ 6278473828221^17*25000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4660851 25000000 6278473828221 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3344456423/5000000000 : ℝ), (3422411199/10000000000 : ℝ), (4660851/25000000 : ℝ)] ![(30425149918937/50000000000000 : ℝ), (26592752494171/100000000000000 : ℝ), (6278473828221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3344456423/5000000000 : ℝ)|^21 ≤ (30425149918937/50000000000000 : ℝ)^17
        have hw : |(3344456423/5000000000 : ℝ)|=(3344456423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3422411199/10000000000 : ℝ)|^21 ≤ (26592752494171/100000000000000 : ℝ)^17
        have hw : |(3422411199/10000000000 : ℝ)|=(3422411199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4660851/25000000 : ℝ)|^21 ≤ (6278473828221/50000000000000 : ℝ)^17
        have hw : |(4660851/25000000 : ℝ)|=(4660851/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-708064901/1250000000 : ℝ)*x 0 + (80949969/400000000 : ℝ)*x 1 + (442729449/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (708064901/1250000000 : ℝ)^21 ≤ (24777288443291/50000000000000 : ℝ)^17 := by
    have hnat : (708064901 : ℕ)^21*50000000000000^17 ≤ 24777288443291^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708064901 1250000000 24777288443291 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80949969/400000000 : ℝ)^21 ≤ (555852340477/4000000000000 : ℝ)^17 := by
    have hnat : (80949969 : ℕ)^21*4000000000000^17 ≤ 555852340477^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80949969 400000000 555852340477 4000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442729449/1000000000 : ℝ)^21 ≤ (18274557292579/50000000000000 : ℝ)^17 := by
    have hnat : (442729449 : ℕ)^21*50000000000000^17 ≤ 18274557292579^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442729449 1000000000 18274557292579 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-708064901/1250000000 : ℝ), (80949969/400000000 : ℝ), (442729449/1000000000 : ℝ)] ![(24777288443291/50000000000000 : ℝ), (555852340477/4000000000000 : ℝ), (18274557292579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-708064901/1250000000 : ℝ)|^21 ≤ (24777288443291/50000000000000 : ℝ)^17
        have hw : |(-708064901/1250000000 : ℝ)|=(708064901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80949969/400000000 : ℝ)|^21 ≤ (555852340477/4000000000000 : ℝ)^17
        have hw : |(80949969/400000000 : ℝ)|=(80949969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442729449/1000000000 : ℝ)|^21 ≤ (18274557292579/50000000000000 : ℝ)^17
        have hw : |(442729449/1000000000 : ℝ)|=(442729449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1694623557/10000000000 : ℝ)*x 0 + (-2036734101/10000000000 : ℝ)*x 1 + (7908167401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1694623557/10000000000 : ℝ)^21 ≤ (2790093234273/25000000000000 : ℝ)^17 := by
    have hnat : (1694623557 : ℕ)^21*25000000000000^17 ≤ 2790093234273^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694623557 10000000000 2790093234273 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036734101/10000000000 : ℝ)^21 ≤ (14006533003003/100000000000000 : ℝ)^17 := by
    have hnat : (2036734101 : ℕ)^21*100000000000000^17 ≤ 14006533003003^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036734101 10000000000 14006533003003 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7908167401/10000000000 : ℝ)^21 ≤ (9354136755823/12500000000000 : ℝ)^17 := by
    have hnat : (7908167401 : ℕ)^21*12500000000000^17 ≤ 9354136755823^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7908167401 10000000000 9354136755823 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1694623557/10000000000 : ℝ), (-2036734101/10000000000 : ℝ), (7908167401/10000000000 : ℝ)] ![(2790093234273/25000000000000 : ℝ), (14006533003003/100000000000000 : ℝ), (9354136755823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1694623557/10000000000 : ℝ)|^21 ≤ (2790093234273/25000000000000 : ℝ)^17
        have hw : |(1694623557/10000000000 : ℝ)|=(1694623557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036734101/10000000000 : ℝ)|^21 ≤ (14006533003003/100000000000000 : ℝ)^17
        have hw : |(-2036734101/10000000000 : ℝ)|=(2036734101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7908167401/10000000000 : ℝ)|^21 ≤ (9354136755823/12500000000000 : ℝ)^17
        have hw : |(7908167401/10000000000 : ℝ)|=(7908167401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4286404011/5000000000 : ℝ)*x 0 + (2419006557/10000000000 : ℝ)*x 1 + (-1/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286404011/5000000000 : ℝ)^21 ≤ (82677503955567/100000000000000 : ℝ)^17 := by
    have hnat : (4286404011 : ℕ)^21*100000000000000^17 ≤ 82677503955567^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286404011 5000000000 82677503955567 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2419006557/10000000000 : ℝ)^21 ≤ (3464499186721/20000000000000 : ℝ)^17 := by
    have hnat : (2419006557 : ℕ)^21*20000000000000^17 ≤ 3464499186721^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419006557 10000000000 3464499186721 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/19531250 : ℝ)^21 ≤ (12323/12500000000000 : ℝ)^17 := by
    have hnat : (1 : ℕ)^21*12500000000000^17 ≤ 12323^17*19531250^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 19531250 12323 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286404011/5000000000 : ℝ), (2419006557/10000000000 : ℝ), (-1/19531250 : ℝ)] ![(82677503955567/100000000000000 : ℝ), (3464499186721/20000000000000 : ℝ), (12323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286404011/5000000000 : ℝ)|^21 ≤ (82677503955567/100000000000000 : ℝ)^17
        have hw : |(4286404011/5000000000 : ℝ)|=(4286404011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2419006557/10000000000 : ℝ)|^21 ≤ (3464499186721/20000000000000 : ℝ)^17
        have hw : |(2419006557/10000000000 : ℝ)|=(2419006557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1/19531250 : ℝ)|^21 ≤ (12323/12500000000000 : ℝ)^17
        have hw : |(-1/19531250 : ℝ)|=(1/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s0_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (583105853/5000000000 : ℝ)*x 0 + (4219075193/5000000000 : ℝ)*x 1 + (1783747639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583105853/5000000000 : ℝ)^21 ≤ (3516945283607/50000000000000 : ℝ)^17 := by
    have hnat : (583105853 : ℕ)^21*50000000000000^17 ≤ 3516945283607^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583105853 5000000000 3516945283607 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219075193/5000000000 : ℝ)^21 ≤ (40538127091147/50000000000000 : ℝ)^17 := by
    have hnat : (4219075193 : ℕ)^21*50000000000000^17 ≤ 40538127091147^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219075193 5000000000 40538127091147 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783747639/10000000000 : ℝ)^21 ≤ (743115952159/6250000000000 : ℝ)^17 := by
    have hnat : (1783747639 : ℕ)^21*6250000000000^17 ≤ 743115952159^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783747639 10000000000 743115952159 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(583105853/5000000000 : ℝ), (4219075193/5000000000 : ℝ), (1783747639/10000000000 : ℝ)] ![(3516945283607/50000000000000 : ℝ), (40538127091147/50000000000000 : ℝ), (743115952159/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(583105853/5000000000 : ℝ)|^21 ≤ (3516945283607/50000000000000 : ℝ)^17
        have hw : |(583105853/5000000000 : ℝ)|=(583105853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219075193/5000000000 : ℝ)|^21 ≤ (40538127091147/50000000000000 : ℝ)^17
        have hw : |(4219075193/5000000000 : ℝ)|=(4219075193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1783747639/10000000000 : ℝ)|^21 ≤ (743115952159/6250000000000 : ℝ)^17
        have hw : |(1783747639/10000000000 : ℝ)|=(1783747639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-809753451/2500000000 : ℝ)*x 0 + (3236561687/10000000000 : ℝ)*x 1 + (2868355059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809753451/2500000000 : ℝ)^21 ≤ (2484367334863/10000000000000 : ℝ)^17 := by
    have hnat : (809753451 : ℕ)^21*10000000000000^17 ≤ 2484367334863^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809753451 2500000000 2484367334863 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3236561687/10000000000 : ℝ)^21 ≤ (496408838437/2000000000000 : ℝ)^17 := by
    have hnat : (3236561687 : ℕ)^21*2000000000000^17 ≤ 496408838437^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3236561687 10000000000 496408838437 2000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2868355059/5000000000 : ℝ)^21 ≤ (25167942357581/50000000000000 : ℝ)^17 := by
    have hnat : (2868355059 : ℕ)^21*50000000000000^17 ≤ 25167942357581^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868355059 5000000000 25167942357581 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-809753451/2500000000 : ℝ), (3236561687/10000000000 : ℝ), (2868355059/5000000000 : ℝ)] ![(2484367334863/10000000000000 : ℝ), (496408838437/2000000000000 : ℝ), (25167942357581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-809753451/2500000000 : ℝ)|^21 ≤ (2484367334863/10000000000000 : ℝ)^17
        have hw : |(-809753451/2500000000 : ℝ)|=(809753451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3236561687/10000000000 : ℝ)|^21 ≤ (496408838437/2000000000000 : ℝ)^17
        have hw : |(3236561687/10000000000 : ℝ)|=(3236561687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2868355059/5000000000 : ℝ)|^21 ≤ (25167942357581/50000000000000 : ℝ)^17
        have hw : |(2868355059/5000000000 : ℝ)|=(2868355059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (202300683/625000000 : ℝ)*x 0 + (-1617149793/5000000000 : ℝ)*x 1 + (5740612217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202300683/625000000 : ℝ)^21 ≤ (2482280304921/10000000000000 : ℝ)^17 := by
    have hnat : (202300683 : ℕ)^21*10000000000000^17 ≤ 2482280304921^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202300683 625000000 2482280304921 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1617149793/5000000000 : ℝ)^21 ≤ (24799014384151/100000000000000 : ℝ)^17 := by
    have hnat : (1617149793 : ℕ)^21*100000000000000^17 ≤ 24799014384151^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617149793 5000000000 24799014384151 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5740612217/10000000000 : ℝ)^21 ≤ (25189091278283/50000000000000 : ℝ)^17 := by
    have hnat : (5740612217 : ℕ)^21*50000000000000^17 ≤ 25189091278283^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5740612217 10000000000 25189091278283 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(202300683/625000000 : ℝ), (-1617149793/5000000000 : ℝ), (5740612217/10000000000 : ℝ)] ![(2482280304921/10000000000000 : ℝ), (24799014384151/100000000000000 : ℝ), (25189091278283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(202300683/625000000 : ℝ)|^21 ≤ (2482280304921/10000000000000 : ℝ)^17
        have hw : |(202300683/625000000 : ℝ)|=(202300683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1617149793/5000000000 : ℝ)|^21 ≤ (24799014384151/100000000000000 : ℝ)^17
        have hw : |(-1617149793/5000000000 : ℝ)|=(1617149793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5740612217/10000000000 : ℝ)|^21 ≤ (25189091278283/50000000000000 : ℝ)^17
        have hw : |(5740612217/10000000000 : ℝ)|=(5740612217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5595875041/10000000000 : ℝ)*x 0 + (5429501041/10000000000 : ℝ)*x 1 + (-762121247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5595875041/10000000000 : ℝ)^21 ≤ (48813824261337/100000000000000 : ℝ)^17 := by
    have hnat : (5595875041 : ℕ)^21*100000000000000^17 ≤ 48813824261337^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595875041 10000000000 48813824261337 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429501041/10000000000 : ℝ)^21 ≤ (47027348208437/100000000000000 : ℝ)^17 := by
    have hnat : (5429501041 : ℕ)^21*100000000000000^17 ≤ 47027348208437^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429501041 10000000000 47027348208437 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (762121247/10000000000 : ℝ)^21 ≤ (4158827520973/100000000000000 : ℝ)^17 := by
    have hnat : (762121247 : ℕ)^21*100000000000000^17 ≤ 4158827520973^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762121247 10000000000 4158827520973 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5595875041/10000000000 : ℝ), (5429501041/10000000000 : ℝ), (-762121247/10000000000 : ℝ)] ![(48813824261337/100000000000000 : ℝ), (47027348208437/100000000000000 : ℝ), (4158827520973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5595875041/10000000000 : ℝ)|^21 ≤ (48813824261337/100000000000000 : ℝ)^17
        have hw : |(5595875041/10000000000 : ℝ)|=(5595875041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429501041/10000000000 : ℝ)|^21 ≤ (47027348208437/100000000000000 : ℝ)^17
        have hw : |(5429501041/10000000000 : ℝ)|=(5429501041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-762121247/10000000000 : ℝ)|^21 ≤ (4158827520973/100000000000000 : ℝ)^17
        have hw : |(-762121247/10000000000 : ℝ)|=(762121247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s1_5 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-21/5000000000 : ℝ)*x 0 + (21/5000000000 : ℝ)*x 1 + (9999999999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21/5000000000 : ℝ)^21 ≤ (4491/100000000000000 : ℝ)^17 := by
    have hnat : (21 : ℕ)^21*100000000000000^17 ≤ 4491^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21 5000000000 4491 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21/5000000000 : ℝ)^21 ≤ (4491/100000000000000 : ℝ)^17 := by
    have hnat : (21 : ℕ)^21*100000000000000^17 ≤ 4491^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21 5000000000 4491 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999999/10000000000 : ℝ)^21 ≤ (1562499999807/1562500000000 : ℝ)^17 := by
    have hnat : (9999999999 : ℕ)^21*1562500000000^17 ≤ 1562499999807^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 1562499999807 1562500000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21/5000000000 : ℝ), (21/5000000000 : ℝ), (9999999999/10000000000 : ℝ)] ![(4491/100000000000000 : ℝ), (4491/100000000000000 : ℝ), (1562499999807/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21/5000000000 : ℝ)|^21 ≤ (4491/100000000000000 : ℝ)^17
        have hw : |(-21/5000000000 : ℝ)|=(21/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21/5000000000 : ℝ)|^21 ≤ (4491/100000000000000 : ℝ)^17
        have hw : |(21/5000000000 : ℝ)|=(21/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9999999999/10000000000 : ℝ)|^21 ≤ (1562499999807/1562500000000 : ℝ)^17
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323059_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4101110369/10000000000 : ℝ)*x 0 + (4598241969/10000000000 : ℝ)*x 1 + (361440781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4101110369/10000000000 : ℝ)^21 ≤ (33252128267577/100000000000000 : ℝ)^17 := by
    have hnat : (4101110369 : ℕ)^21*100000000000000^17 ≤ 33252128267577^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101110369 10000000000 33252128267577 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4598241969/10000000000 : ℝ)^21 ≤ (19150127313463/50000000000000 : ℝ)^17 := by
    have hnat : (4598241969 : ℕ)^21*50000000000000^17 ≤ 19150127313463^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4598241969 10000000000 19150127313463 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361440781/1000000000 : ℝ)^21 ≤ (28447617089867/100000000000000 : ℝ)^17 := by
    have hnat : (361440781 : ℕ)^21*100000000000000^17 ≤ 28447617089867^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361440781 1000000000 28447617089867 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4101110369/10000000000 : ℝ), (4598241969/10000000000 : ℝ), (361440781/1000000000 : ℝ)] ![(33252128267577/100000000000000 : ℝ), (19150127313463/50000000000000 : ℝ), (28447617089867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4101110369/10000000000 : ℝ)|^21 ≤ (33252128267577/100000000000000 : ℝ)^17
        have hw : |(4101110369/10000000000 : ℝ)|=(4101110369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4598241969/10000000000 : ℝ)|^21 ≤ (19150127313463/50000000000000 : ℝ)^17
        have hw : |(4598241969/10000000000 : ℝ)|=(4598241969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361440781/1000000000 : ℝ)|^21 ≤ (28447617089867/100000000000000 : ℝ)^17
        have hw : |(361440781/1000000000 : ℝ)|=(361440781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323059 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (285913930952523/2000000000000000 : ℝ)) (beta := (929198400367553/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(285913930952523/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(929198400367553/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-117842759/400000000 : ℝ)*X 0 0+(2946068669/10000000000 : ℝ)*X 0 1+(623613883/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1473034577/5000000000 : ℝ)*X 1 0+(-294606873/1000000000 : ℝ)*X 1 1+(1559034657/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1460334443/5000000000 : ℝ)*X 0 0+(1283279769/2000000000 : ℝ)*X 0 1+(2754176877/10000000000 : ℝ)*X 0 2+(1460334443/5000000000 : ℝ)*X 1 0+(1283279769/2000000000 : ℝ)*X 1 1+(2754176877/10000000000 : ℝ)*X 1 2+(1460334443/5000000000 : ℝ)*X 2 0+(1283279769/2000000000 : ℝ)*X 2 1+(2754176877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2226707161/10000000000 : ℝ)*X 0 0+(138155927/2500000000 : ℝ)*X 0 1+(8479420311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((153444497/1000000000 : ℝ)*X 1 0+(-42729171/312500000 : ℝ)*X 1 1+(8479419449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((420800027/1000000000 : ℝ)*X 2 0+(3557343279/5000000000 : ℝ)*X 2 1+(-520481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1882197843/10000000000 : ℝ)*X 0 0+(4085744659/5000000000 : ℝ)*X 0 1+(147110669/1000000000 : ℝ)*X 0 2+(1882197843/10000000000 : ℝ)*X 1 0+(4085744659/5000000000 : ℝ)*X 1 1+(147110669/1000000000 : ℝ)*X 1 2+(1882197843/10000000000 : ℝ)*X 2 0+(4085744659/5000000000 : ℝ)*X 2 1+(147110669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-966521069/10000000000 : ℝ)*X 0 0+(1827201891/10000000000 : ℝ)*X 0 1+(8530506863/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((217282833/2500000000 : ℝ)*X 1 0+(-1909589929/10000000000 : ℝ)*X 1 1+(4265252197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((847658059/1000000000 : ℝ)*X 2 0+(636897177/2500000000 : ℝ)*X 2 1+(-449673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3344456423/5000000000 : ℝ)*X 0 0+(3422411199/10000000000 : ℝ)*X 0 1+(4660851/25000000 : ℝ)*X 0 2+(3344456423/5000000000 : ℝ)*X 1 0+(3422411199/10000000000 : ℝ)*X 1 1+(4660851/25000000 : ℝ)*X 1 2+(3344456423/5000000000 : ℝ)*X 2 0+(3422411199/10000000000 : ℝ)*X 2 1+(4660851/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-708064901/1250000000 : ℝ)*X 0 0+(80949969/400000000 : ℝ)*X 0 1+(442729449/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1694623557/10000000000 : ℝ)*X 1 0+(-2036734101/10000000000 : ℝ)*X 1 1+(7908167401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4286404011/5000000000 : ℝ)*X 2 0+(2419006557/10000000000 : ℝ)*X 2 1+(-1/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((583105853/5000000000 : ℝ)*X 0 0+(4219075193/5000000000 : ℝ)*X 0 1+(1783747639/10000000000 : ℝ)*X 0 2+(583105853/5000000000 : ℝ)*X 1 0+(4219075193/5000000000 : ℝ)*X 1 1+(1783747639/10000000000 : ℝ)*X 1 2+(583105853/5000000000 : ℝ)*X 2 0+(4219075193/5000000000 : ℝ)*X 2 1+(1783747639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((17447/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17447/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13987394935186185825357/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289233742517/250000000000 : ℝ)*(base7) + (550111/1000000000000 : ℝ)*(base29) + (144321/1000000000000 : ℝ)*(base60) + (1534405906187/1000000000000 : ℝ)*(major_s0_0) + (1534405906187/1000000000000 : ℝ)*(major_s0_1) + (1534405906187/1000000000000 : ℝ)*(major_s0_2) + (1927341/1000000000000 : ℝ)*(sp_s0_0) + (1640898081101/1000000000000 : ℝ)*(sp_s0_7) + (820456696593/500000000000 : ℝ)*(sp_s0_8) + (1640916968919/1000000000000 : ℝ)*(sp_s0_9) + (242655004093/125000000000 : ℝ)*(sp_s0_13) + (8480239/500000000000 : ℝ)*(sp_s0_14) + (1787867/500000000000 : ℝ)*(sp_s0_22) + (4787469/250000000000 : ℝ)*(sp_s0_27) + (784324762663/1000000000000 : ℝ)*(f.failure) + (1640916968919/1000000000000 : ℝ)*(f.sum) + (204130107/1000000000000000000000 : ℝ)*base63 + (6169271426249589/10000000000000000000000000000 : ℝ)*base64 + (6905759242249589/10000000000000000000000000000 : ℝ)*base66 + (398553870159801/2000000000000000000000000000 : ℝ)*base68 + (310756190056323/1250000000000000000000000000 : ℝ)*base70 + (7139527135249589/10000000000000000000000000000 : ℝ)*base72 + (166483666640199/2000000000000000000000000000 : ℝ)*base74 + (754712417040199/2000000000000000000000000000 : ℝ)*base76 + (73980127749589/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (56671/50000000000000000 : ℝ)*base87 + (56671/50000000000000000 : ℝ)*base89 + (56671/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69459/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69459/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8921786155953707512767/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105411912581/250000000000 : ℝ)*(base5) + (1155903508107/1000000000000 : ℝ)*(base7) + (2756311/1000000000000 : ℝ)*(base19) + (73772798411/500000000000 : ℝ)*(base60) + (1510885641497/1000000000000 : ℝ)*(major_s0_0) + (1510885641497/1000000000000 : ℝ)*(major_s0_1) + (1510885641497/1000000000000 : ℝ)*(major_s0_2) + (14287/31250000000 : ℝ)*(sp_s0_0) + (11088913/500000000000 : ℝ)*(sp_s0_8) + (3212946029/2000000000 : ℝ)*(sp_s0_14) + (1606448537547/1000000000000 : ℝ)*(sp_s0_15) + (2028067614191/1000000000000 : ℝ)*(sp_s0_16) + (753279017531/500000000000 : ℝ)*(sp_s0_20) + (26753909/500000000000 : ℝ)*(sp_s0_23) + (772302177279/1000000000000 : ℝ)*(f.failure) + (401618367921/250000000000 : ℝ)*(f.sum) + (14678743/156250000000000000000 : ℝ)*base62 + (2635691944853159/10000000000000000000000000000 : ℝ)*base64 + (2829918030853159/10000000000000000000000000000 : ℝ)*base66 + (523189960846931/2000000000000000000000000000 : ℝ)*base68 + (161620348202313/1250000000000000000000000000 : ℝ)*base70 + (2064969202853159/10000000000000000000000000000 : ℝ)*base72 + (2100217921953069/2000000000000000000000000000 : ℝ)*base74 + (1009998332753069/2000000000000000000000000000 : ℝ)*base76 + (198941231353159/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (49943/50000000000000000 : ℝ)*base87 + (49943/50000000000000000 : ℝ)*base89 + (49943/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26283/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26283/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2099269849796715242799/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37981620717/62500000000 : ℝ)*(base7) + (531597/250000000000 : ℝ)*(base40) + (5225882333/8000000000 : ℝ)*(base44) + (90978985773/1000000000000 : ℝ)*(base50) + (60661976743/40000000000 : ℝ)*(major_s0_0) + (17266282539/20000000000 : ℝ)*(major_s0_1) + (60661976743/40000000000 : ℝ)*(major_s0_2) + (62365843/1000000000000 : ℝ)*(sp_s0_1) + (769159/62500000000 : ℝ)*(sp_s0_6) + (189838653/1000000000000 : ℝ)*(sp_s0_16) + (1919849494263/1000000000000 : ℝ)*(sp_s0_21) + (316637959199/250000000000 : ℝ)*(sp_s0_22) + (191965965561/100000000000 : ℝ)*(sp_s0_23) + (729655598899/1000000000000 : ℝ)*(sp_s0_27) + (155039453119/200000000000 : ℝ)*(f.failure) + (1919849494263/1000000000000 : ℝ)*(f.sum) + (211875765441/16000000000000000000000000 : ℝ)*base63 + (180847776940121/400000000000000000000000000 : ℝ)*base64 + (27175322322933/200000000000000000000000000 : ℝ)*base66 + (1893841851411/80000000000000000000000000 : ℝ)*base69 + (19717852829647/50000000000000000000000000 : ℝ)*base70 + (27606611859879/400000000000000000000000000 : ℝ)*base73 + (26294111423897/40000000000000000000000000 : ℝ)*base75 + (50678991131411/80000000000000000000000000 : ℝ)*base76 + (87976160465987/400000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (8777/10000000000000000 : ℝ)*base86 + (8777/10000000000000000 : ℝ)*base88 + (8777/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (17447/25000 : ℝ) ^ (83/16 : ℝ) ≤ (15474358463063180183/100000000000000000000 : ℝ) := by
    have hpowers : (17447/25000 : ℝ)^83 ≤ (15474358463063180183/100000000000000000000 : ℝ)^16 := by
      have hnat : (17447 : ℕ)^83*100000000000000000000^16 ≤ 15474358463063180183^16*25000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17447 25000 15474358463063180183 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17447/25000 : ℝ)) (X := (15474358463063180183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (115474358463063180183/100000000000000000000 : ℝ) ≤ (10281237906805667/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (115474358463063180183/100000000000000000000 : ℝ)^16 ≤ (10281237906805667/10000000000000000 : ℝ)^83 := by
      have hnat : (115474358463063180183 : ℕ)^16*10000000000000000^83 ≤ 10281237906805667^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115474358463063180183 100000000000000000000 10281237906805667 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10281237906805667/10000000000000000 : ℝ)) (X := (115474358463063180183/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (65474358463063180183/50000000000000000000 : ℝ) ≤ (10533525099651503/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (65474358463063180183/50000000000000000000 : ℝ)^16 ≤ (10533525099651503/10000000000000000 : ℝ)^83 := by
      have hnat : (65474358463063180183 : ℕ)^16*10000000000000000^83 ≤ 10533525099651503^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65474358463063180183 50000000000000000000 10533525099651503 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10533525099651503/10000000000000000 : ℝ)) (X := (65474358463063180183/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(281237906805667/6978800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(63071798211459/1744700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (17447/25000 : ℝ)) (alpha := (281237906805667/6978800000000000 : ℝ)) (beta := (63071798211459/1744700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17447/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(281237906805667/6978800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(63071798211459/1744700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (69459/100000 : ℝ) ^ (83/16 : ℝ) ≤ (15099644799279682157/100000000000000000000 : ℝ) := by
    have hpowers : (69459/100000 : ℝ)^83 ≤ (15099644799279682157/100000000000000000000 : ℝ)^16 := by
      have hnat : (69459 : ℕ)^83*100000000000000000000^16 ≤ 15099644799279682157^16*100000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69459 100000 15099644799279682157 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69459/100000 : ℝ)) (X := (15099644799279682157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (115099644799279682157/100000000000000000000 : ℝ) ≤ (10274798129954349/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (115099644799279682157/100000000000000000000 : ℝ)^16 ≤ (10274798129954349/10000000000000000 : ℝ)^83 := by
      have hnat : (115099644799279682157 : ℕ)^16*10000000000000000^83 ≤ 10274798129954349^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115099644799279682157 100000000000000000000 10274798129954349 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10274798129954349/10000000000000000 : ℝ)) (X := (115099644799279682157/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (65099644799279682157/50000000000000000000 : ℝ) ≤ (5260938576251479/5000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (65099644799279682157/50000000000000000000 : ℝ)^16 ≤ (5260938576251479/5000000000000000 : ℝ)^83 := by
      have hnat : (65099644799279682157 : ℕ)^16*5000000000000000^83 ≤ 5260938576251479^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65099644799279682157 50000000000000000000 5260938576251479 5000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5260938576251479/5000000000000000 : ℝ)) (X := (65099644799279682157/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(274798129954349/6945900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(247079022548609/6945900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (69459/100000 : ℝ)) (alpha := (274798129954349/6945900000000000 : ℝ)) (beta := (247079022548609/6945900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (69459/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(274798129954349/6945900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(247079022548609/6945900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (26283/50000 : ℝ) ^ (83/16 : ℝ) ≤ (711519527599245547/20000000000000000000 : ℝ) := by
    have hpowers : (26283/50000 : ℝ)^83 ≤ (711519527599245547/20000000000000000000 : ℝ)^16 := by
      have hnat : (26283 : ℕ)^83*20000000000000000000^16 ≤ 711519527599245547^16*50000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26283 50000 711519527599245547 20000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26283/50000 : ℝ)) (X := (711519527599245547/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20711519527599245547/20000000000000000000 : ℝ) ≤ (314613001410781/312500000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (20711519527599245547/20000000000000000000 : ℝ)^16 ≤ (314613001410781/312500000000000 : ℝ)^83 := by
      have hnat : (20711519527599245547 : ℕ)^16*312500000000000^83 ≤ 314613001410781^83*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20711519527599245547 20000000000000000000 314613001410781 312500000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314613001410781/312500000000000 : ℝ)) (X := (20711519527599245547/20000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10711519527599245547/10000000000000000000 : ℝ) ≤ (2026676452106439/2000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (10711519527599245547/10000000000000000000 : ℝ)^16 ≤ (2026676452106439/2000000000000000 : ℝ)^83 := by
      have hnat : (10711519527599245547 : ℕ)^16*2000000000000000^83 ≤ 2026676452106439^83*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10711519527599245547 10000000000000000000 2026676452106439 2000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2026676452106439/2000000000000000 : ℝ)) (X := (10711519527599245547/10000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2113001410781/164268750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(65766215387203/5256600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (26283/50000 : ℝ)) (alpha := (2113001410781/164268750000000 : ℝ)) (beta := (65766215387203/5256600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (26283/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2113001410781/164268750000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(65766215387203/5256600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-809753451/2500000000 : ℝ)*X 0 0+(3236561687/10000000000 : ℝ)*X 0 1+(2868355059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((202300683/625000000 : ℝ)*X 1 0+(-1617149793/5000000000 : ℝ)*X 1 1+(5740612217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5595875041/10000000000 : ℝ)*X 2 0+(5429501041/10000000000 : ℝ)*X 2 1+(-762121247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_5 : ((-21/5000000000 : ℝ)*X 0 0+(21/5000000000 : ℝ)*X 0 1+(9999999999/10000000000 : ℝ)*X 0 2+(-21/5000000000 : ℝ)*X 1 0+(21/5000000000 : ℝ)*X 1 1+(9999999999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s1_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4101110369/10000000000 : ℝ)*X 0 0+(4598241969/10000000000 : ℝ)*X 0 1+(361440781/1000000000 : ℝ)*X 0 2+(4101110369/10000000000 : ℝ)*X 1 0+(4598241969/10000000000 : ℝ)*X 1 1+(361440781/1000000000 : ℝ)*X 1 2+(4101110369/10000000000 : ℝ)*X 2 0+(4598241969/10000000000 : ℝ)*X 2 1+(361440781/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-218451/25000 : ℝ) < ((-97817/50000 : ℝ)*P 0+(-97817/50000 : ℝ)*P 1+(-97817/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-218451/25000 : ℝ) < (-88281656790196777493774901005999/10142171650000000000000000000000 : ℝ) := by norm_num
    linear_combination (26871/250000000000 : ℝ)*(base13) + (25301/125000000000 : ℝ)*(base15) + (19351/200000000000 : ℝ)*(base23) + (33107/500000000000 : ℝ)*(base39) + (3643/500000000000 : ℝ)*(base44) + (34119/1000000000000 : ℝ)*(base50) + (7273911233/12500000000 : ℝ)*(base60) + (97817/50000 : ℝ)*(major_s1_0) + (978169996357/500000000000 : ℝ)*(major_s1_1) + (978170571319/500000000000 : ℝ)*(major_s1_2) + (45335485793/15625000000 : ℝ)*(sp_s1_0) + (1450735494271/500000000000 : ℝ)*(sp_s1_1) + (2901471101481/1000000000000 : ℝ)*(sp_s1_2) + (571319/500000000000 : ℝ)*(sp_s1_5) + (499999996357/500000000000 : ℝ)*(sp_s1_6) + (725367799559/250000000000 : ℝ)*(f.sum) + (10041118284181743689/30426514950000000000000000000000 : ℝ)*base62 + (1380026225171377/2628300000000000000000000000 : ℝ)*base65 + (1519786215612203/3472950000000000000000000000 : ℝ)*base67 + (60377755120657/657075000000000000000000000 : ℝ)*base68 + (3520408879913943121/45855950100000000000000000000000 : ℝ)*base70 + (927279037563/43617500000000000000000000 : ℝ)*base72 + (205793908575643/868237500000000000000000000 : ℝ)*base74 + (101924149973611/174470000000000000000000000 : ℝ)*base77 + (4592909734516571783/30296279325000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p023_b034 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c323059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p023_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
