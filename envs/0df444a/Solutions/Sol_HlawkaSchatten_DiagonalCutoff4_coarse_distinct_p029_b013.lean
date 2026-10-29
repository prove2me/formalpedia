-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b013
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:26:41.547418+00:00
-- url     : https://prove2.me/submissions/2d84952d-0cba-40e2-86d7-172a2bd3d00c

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
theorem collision_support_c329031_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-125470709/400000000 : ℝ)*x 0 + (5189786851/10000000000 : ℝ)*x 1 + (3649409007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125470709/400000000 : ℝ)^95 ≤ (24802993799247/100000000000000 : ℝ)^79 := by
    have hnat : (125470709 : ℕ)^95*100000000000000^79 ≤ 24802993799247^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125470709 400000000 24802993799247 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189786851/10000000000 : ℝ)^95 ≤ (5680261089033/12500000000000 : ℝ)^79 := by
    have hnat : (5189786851 : ℕ)^95*12500000000000^79 ≤ 5680261089033^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189786851 10000000000 5680261089033 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3649409007/10000000000 : ℝ)^95 ≤ (929841171187/3125000000000 : ℝ)^79 := by
    have hnat : (3649409007 : ℕ)^95*3125000000000^79 ≤ 929841171187^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3649409007 10000000000 929841171187 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125470709/400000000 : ℝ), (5189786851/10000000000 : ℝ), (3649409007/10000000000 : ℝ)] ![(24802993799247/100000000000000 : ℝ), (5680261089033/12500000000000 : ℝ), (929841171187/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125470709/400000000 : ℝ)|^95 ≤ (24802993799247/100000000000000 : ℝ)^79
        have hw : |(-125470709/400000000 : ℝ)|=(125470709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189786851/10000000000 : ℝ)|^95 ≤ (5680261089033/12500000000000 : ℝ)^79
        have hw : |(5189786851/10000000000 : ℝ)|=(5189786851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3649409007/10000000000 : ℝ)|^95 ≤ (929841171187/3125000000000 : ℝ)^79
        have hw : |(3649409007/10000000000 : ℝ)|=(3649409007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3135424529/5000000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (618962941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3135424529/5000000000 : ℝ)^95 ≤ (57053004350697/100000000000000 : ℝ)^79 := by
    have hnat : (3135424529 : ℕ)^95*100000000000000^79 ≤ 57053004350697^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135424529 5000000000 57053004350697 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^95 ≤ (0 : ℝ)^79 := by
    have hnat : (0 : ℕ)^95*1^79 ≤ 0^79*1^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (618962941/1250000000 : ℝ)^95 ≤ (5368374455823/12500000000000 : ℝ)^79 := by
    have hnat : (618962941 : ℕ)^95*12500000000000^79 ≤ 5368374455823^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618962941 1250000000 5368374455823 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3135424529/5000000000 : ℝ), (0 : ℝ), (618962941/1250000000 : ℝ)] ![(57053004350697/100000000000000 : ℝ), (0 : ℝ), (5368374455823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3135424529/5000000000 : ℝ)|^95 ≤ (57053004350697/100000000000000 : ℝ)^79
        have hw : |(3135424529/5000000000 : ℝ)|=(3135424529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^95 ≤ (0 : ℝ)^79
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(618962941/1250000000 : ℝ)|^95 ≤ (5368374455823/12500000000000 : ℝ)^79
        have hw : |(618962941/1250000000 : ℝ)|=(618962941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2598847661/10000000000 : ℝ)*x 0 + (6176459627/10000000000 : ℝ)*x 1 + (-3072881567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598847661/10000000000 : ℝ)^95 ≤ (19781326891741/100000000000000 : ℝ)^79 := by
    have hnat : (2598847661 : ℕ)^95*100000000000000^79 ≤ 19781326891741^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598847661 10000000000 19781326891741 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6176459627/10000000000 : ℝ)^95 ≤ (56021889839727/100000000000000 : ℝ)^79 := by
    have hnat : (6176459627 : ℕ)^95*100000000000000^79 ≤ 56021889839727^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6176459627 10000000000 56021889839727 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3072881567/10000000000 : ℝ)^95 ≤ (24196783261951/100000000000000 : ℝ)^79 := by
    have hnat : (3072881567 : ℕ)^95*100000000000000^79 ≤ 24196783261951^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3072881567 10000000000 24196783261951 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598847661/10000000000 : ℝ), (6176459627/10000000000 : ℝ), (-3072881567/10000000000 : ℝ)] ![(19781326891741/100000000000000 : ℝ), (56021889839727/100000000000000 : ℝ), (24196783261951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598847661/10000000000 : ℝ)|^95 ≤ (19781326891741/100000000000000 : ℝ)^79
        have hw : |(2598847661/10000000000 : ℝ)|=(2598847661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6176459627/10000000000 : ℝ)|^95 ≤ (56021889839727/100000000000000 : ℝ)^79
        have hw : |(6176459627/10000000000 : ℝ)|=(6176459627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3072881567/10000000000 : ℝ)|^95 ≤ (24196783261951/100000000000000 : ℝ)^79
        have hw : |(-3072881567/10000000000 : ℝ)|=(3072881567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-696992369/2000000000 : ℝ)*x 0 + (233555559/1000000000 : ℝ)*x 1 + (3016147373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (696992369/2000000000 : ℝ)^95 ≤ (28150015659811/100000000000000 : ℝ)^79 := by
    have hnat : (696992369 : ℕ)^95*100000000000000^79 ≤ 28150015659811^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696992369 2000000000 28150015659811 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233555559/1000000000 : ℝ)^95 ≤ (17396794695237/100000000000000 : ℝ)^79 := by
    have hnat : (233555559 : ℕ)^95*100000000000000^79 ≤ 17396794695237^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233555559 1000000000 17396794695237 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3016147373/5000000000 : ℝ)^95 ≤ (13613297408343/25000000000000 : ℝ)^79 := by
    have hnat : (3016147373 : ℕ)^95*25000000000000^79 ≤ 13613297408343^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016147373 5000000000 13613297408343 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-696992369/2000000000 : ℝ), (233555559/1000000000 : ℝ), (3016147373/5000000000 : ℝ)] ![(28150015659811/100000000000000 : ℝ), (17396794695237/100000000000000 : ℝ), (13613297408343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-696992369/2000000000 : ℝ)|^95 ≤ (28150015659811/100000000000000 : ℝ)^79
        have hw : |(-696992369/2000000000 : ℝ)|=(696992369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233555559/1000000000 : ℝ)|^95 ≤ (17396794695237/100000000000000 : ℝ)^79
        have hw : |(233555559/1000000000 : ℝ)|=(233555559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3016147373/5000000000 : ℝ)|^95 ≤ (13613297408343/25000000000000 : ℝ)^79
        have hw : |(3016147373/5000000000 : ℝ)|=(3016147373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4871486167/10000000000 : ℝ)*x 0 + (507/2000000000 : ℝ)*x 1 + (6347099941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4871486167/10000000000 : ℝ)^95 ≤ (42111725620851/100000000000000 : ℝ)^79 := by
    have hnat : (4871486167 : ℕ)^95*100000000000000^79 ≤ 42111725620851^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871486167 10000000000 42111725620851 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507/2000000000 : ℝ)^95 ≤ (1169701/100000000000000 : ℝ)^79 := by
    have hnat : (507 : ℕ)^95*100000000000000^79 ≤ 1169701^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507 2000000000 1169701 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6347099941/10000000000 : ℝ)^95 ≤ (11577654640081/20000000000000 : ℝ)^79 := by
    have hnat : (6347099941 : ℕ)^95*20000000000000^79 ≤ 11577654640081^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6347099941 10000000000 11577654640081 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4871486167/10000000000 : ℝ), (507/2000000000 : ℝ), (6347099941/10000000000 : ℝ)] ![(42111725620851/100000000000000 : ℝ), (1169701/100000000000000 : ℝ), (11577654640081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4871486167/10000000000 : ℝ)|^95 ≤ (42111725620851/100000000000000 : ℝ)^79
        have hw : |(4871486167/10000000000 : ℝ)|=(4871486167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(507/2000000000 : ℝ)|^95 ≤ (1169701/100000000000000 : ℝ)^79
        have hw : |(507/2000000000 : ℝ)|=(507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6347099941/10000000000 : ℝ)|^95 ≤ (11577654640081/20000000000000 : ℝ)^79
        have hw : |(6347099941/10000000000 : ℝ)|=(6347099941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (226207899/2000000000 : ℝ)*x 0 + (1023760613/1250000000 : ℝ)*x 1 + (-1957772827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226207899/2000000000 : ℝ)^95 ≤ (7274063126637/100000000000000 : ℝ)^79 := by
    have hnat : (226207899 : ℕ)^95*100000000000000^79 ≤ 7274063126637^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226207899 2000000000 7274063126637 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023760613/1250000000 : ℝ)^95 ≤ (2457970031067/3125000000000 : ℝ)^79 := by
    have hnat : (1023760613 : ℕ)^95*3125000000000^79 ≤ 2457970031067^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023760613 1250000000 2457970031067 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1957772827/10000000000 : ℝ)^95 ≤ (7035447930673/50000000000000 : ℝ)^79 := by
    have hnat : (1957772827 : ℕ)^95*50000000000000^79 ≤ 7035447930673^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957772827 10000000000 7035447930673 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(226207899/2000000000 : ℝ), (1023760613/1250000000 : ℝ), (-1957772827/10000000000 : ℝ)] ![(7274063126637/100000000000000 : ℝ), (2457970031067/3125000000000 : ℝ), (7035447930673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(226207899/2000000000 : ℝ)|^95 ≤ (7274063126637/100000000000000 : ℝ)^79
        have hw : |(226207899/2000000000 : ℝ)|=(226207899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023760613/1250000000 : ℝ)|^95 ≤ (2457970031067/3125000000000 : ℝ)^79
        have hw : |(1023760613/1250000000 : ℝ)|=(1023760613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1957772827/10000000000 : ℝ)|^95 ≤ (7035447930673/50000000000000 : ℝ)^79
        have hw : |(-1957772827/10000000000 : ℝ)|=(1957772827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2250050693/10000000000 : ℝ)*x 0 + (6584419081/10000000000 : ℝ)*x 1 + (2931609807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2250050693/10000000000 : ℝ)^95 ≤ (16633771981829/100000000000000 : ℝ)^79 := by
    have hnat : (2250050693 : ℕ)^95*100000000000000^79 ≤ 16633771981829^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250050693 10000000000 16633771981829 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6584419081/10000000000 : ℝ)^95 ≤ (60500854460947/100000000000000 : ℝ)^79 := by
    have hnat : (6584419081 : ℕ)^95*100000000000000^79 ≤ 60500854460947^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6584419081 10000000000 60500854460947 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2931609807/10000000000 : ℝ)^95 ≤ (22865373544467/100000000000000 : ℝ)^79 := by
    have hnat : (2931609807 : ℕ)^95*100000000000000^79 ≤ 22865373544467^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2931609807 10000000000 22865373544467 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2250050693/10000000000 : ℝ), (6584419081/10000000000 : ℝ), (2931609807/10000000000 : ℝ)] ![(16633771981829/100000000000000 : ℝ), (60500854460947/100000000000000 : ℝ), (22865373544467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2250050693/10000000000 : ℝ)|^95 ≤ (16633771981829/100000000000000 : ℝ)^79
        have hw : |(2250050693/10000000000 : ℝ)|=(2250050693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6584419081/10000000000 : ℝ)|^95 ≤ (60500854460947/100000000000000 : ℝ)^79
        have hw : |(6584419081/10000000000 : ℝ)|=(6584419081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2931609807/10000000000 : ℝ)|^95 ≤ (22865373544467/100000000000000 : ℝ)^79
        have hw : |(2931609807/10000000000 : ℝ)|=(2931609807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4152370249/10000000000 : ℝ)*x 0 + (1510232819/5000000000 : ℝ)*x 1 + (963399759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152370249/10000000000 : ℝ)^95 ≤ (34752731565557/100000000000000 : ℝ)^79 := by
    have hnat : (4152370249 : ℕ)^95*100000000000000^79 ≤ 34752731565557^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152370249 10000000000 34752731565557 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510232819/5000000000 : ℝ)^95 ≤ (5925328318679/25000000000000 : ℝ)^79 := by
    have hnat : (1510232819 : ℕ)^95*25000000000000^79 ≤ 5925328318679^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510232819 5000000000 5925328318679 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963399759/2000000000 : ℝ)^95 ≤ (519324439251/1250000000000 : ℝ)^79 := by
    have hnat : (963399759 : ℕ)^95*1250000000000^79 ≤ 519324439251^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963399759 2000000000 519324439251 1250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4152370249/10000000000 : ℝ), (1510232819/5000000000 : ℝ), (963399759/2000000000 : ℝ)] ![(34752731565557/100000000000000 : ℝ), (5925328318679/25000000000000 : ℝ), (519324439251/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4152370249/10000000000 : ℝ)|^95 ≤ (34752731565557/100000000000000 : ℝ)^79
        have hw : |(-4152370249/10000000000 : ℝ)|=(4152370249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510232819/5000000000 : ℝ)|^95 ≤ (5925328318679/25000000000000 : ℝ)^79
        have hw : |(1510232819/5000000000 : ℝ)|=(1510232819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963399759/2000000000 : ℝ)|^95 ≤ (519324439251/1250000000000 : ℝ)^79
        have hw : |(963399759/2000000000 : ℝ)|=(963399759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1030705537/1250000000 : ℝ)*x 0 + (6149/1000000000 : ℝ)*x 1 + (1349567489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030705537/1250000000 : ℝ)^95 ≤ (4956070128549/6250000000000 : ℝ)^79 := by
    have hnat : (1030705537 : ℕ)^95*6250000000000^79 ≤ 4956070128549^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030705537 1250000000 4956070128549 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6149/1000000000 : ℝ)^95 ≤ (54121833/100000000000000 : ℝ)^79 := by
    have hnat : (6149 : ℕ)^95*100000000000000^79 ≤ 54121833^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6149 1000000000 54121833 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349567489/5000000000 : ℝ)^95 ≤ (2070282381339/10000000000000 : ℝ)^79 := by
    have hnat : (1349567489 : ℕ)^95*10000000000000^79 ≤ 2070282381339^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349567489 5000000000 2070282381339 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030705537/1250000000 : ℝ), (6149/1000000000 : ℝ), (1349567489/5000000000 : ℝ)] ![(4956070128549/6250000000000 : ℝ), (54121833/100000000000000 : ℝ), (2070282381339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030705537/1250000000 : ℝ)|^95 ≤ (4956070128549/6250000000000 : ℝ)^79
        have hw : |(1030705537/1250000000 : ℝ)|=(1030705537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6149/1000000000 : ℝ)|^95 ≤ (54121833/100000000000000 : ℝ)^79
        have hw : |(6149/1000000000 : ℝ)|=(6149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349567489/5000000000 : ℝ)|^95 ≤ (2070282381339/10000000000000 : ℝ)^79
        have hw : |(1349567489/5000000000 : ℝ)|=(1349567489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (224234771/2500000000 : ℝ)*x 0 + (134351279/200000000 : ℝ)*x 1 + (-3929410817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224234771/2500000000 : ℝ)^95 ≤ (5503821057047/100000000000000 : ℝ)^79 := by
    have hnat : (224234771 : ℕ)^95*100000000000000^79 ≤ 5503821057047^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224234771 2500000000 5503821057047 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134351279/200000000 : ℝ)^95 ≤ (61975028189429/100000000000000 : ℝ)^79 := by
    have hnat : (134351279 : ℕ)^95*100000000000000^79 ≤ 61975028189429^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134351279 200000000 61975028189429 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3929410817/10000000000 : ℝ)^95 ≤ (16260575371883/50000000000000 : ℝ)^79 := by
    have hnat : (3929410817 : ℕ)^95*50000000000000^79 ≤ 16260575371883^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929410817 10000000000 16260575371883 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224234771/2500000000 : ℝ), (134351279/200000000 : ℝ), (-3929410817/10000000000 : ℝ)] ![(5503821057047/100000000000000 : ℝ), (61975028189429/100000000000000 : ℝ), (16260575371883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224234771/2500000000 : ℝ)|^95 ≤ (5503821057047/100000000000000 : ℝ)^79
        have hw : |(224234771/2500000000 : ℝ)|=(224234771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134351279/200000000 : ℝ)|^95 ≤ (61975028189429/100000000000000 : ℝ)^79
        have hw : |(134351279/200000000 : ℝ)|=(134351279/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3929410817/10000000000 : ℝ)|^95 ≤ (16260575371883/50000000000000 : ℝ)^79
        have hw : |(-3929410817/10000000000 : ℝ)|=(3929410817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2079676449/10000000000 : ℝ)*x 0 + (1082220353/2500000000 : ℝ)*x 1 + (5462830777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079676449/10000000000 : ℝ)^95 ≤ (3782756134003/25000000000000 : ℝ)^79 := by
    have hnat : (2079676449 : ℕ)^95*25000000000000^79 ≤ 3782756134003^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079676449 10000000000 3782756134003 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082220353/2500000000 : ℝ)^95 ≤ (3653677901857/10000000000000 : ℝ)^79 := by
    have hnat : (1082220353 : ℕ)^95*10000000000000^79 ≤ 3653677901857^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082220353 2500000000 3653677901857 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462830777/10000000000 : ℝ)^95 ≤ (24166098212647/50000000000000 : ℝ)^79 := by
    have hnat : (5462830777 : ℕ)^95*50000000000000^79 ≤ 24166098212647^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462830777 10000000000 24166098212647 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079676449/10000000000 : ℝ), (1082220353/2500000000 : ℝ), (5462830777/10000000000 : ℝ)] ![(3782756134003/25000000000000 : ℝ), (3653677901857/10000000000000 : ℝ), (24166098212647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079676449/10000000000 : ℝ)|^95 ≤ (3782756134003/25000000000000 : ℝ)^79
        have hw : |(2079676449/10000000000 : ℝ)|=(2079676449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082220353/2500000000 : ℝ)|^95 ≤ (3653677901857/10000000000000 : ℝ)^79
        have hw : |(1082220353/2500000000 : ℝ)|=(1082220353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462830777/10000000000 : ℝ)|^95 ≤ (24166098212647/50000000000000 : ℝ)^79
        have hw : |(5462830777/10000000000 : ℝ)|=(5462830777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-151490709/1000000000 : ℝ)*x 0 + (6266937327/10000000000 : ℝ)*x 1 + (3942648053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151490709/1000000000 : ℝ)^95 ≤ (2584212568109/25000000000000 : ℝ)^79 := by
    have hnat : (151490709 : ℕ)^95*25000000000000^79 ≤ 2584212568109^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151490709 1000000000 2584212568109 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6266937327/10000000000 : ℝ)^95 ≤ (44539226271/78125000000 : ℝ)^79 := by
    have hnat : (6266937327 : ℕ)^95*78125000000^79 ≤ 44539226271^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6266937327 10000000000 44539226271 78125000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3942648053/10000000000 : ℝ)^95 ≤ (4081617510789/12500000000000 : ℝ)^79 := by
    have hnat : (3942648053 : ℕ)^95*12500000000000^79 ≤ 4081617510789^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3942648053 10000000000 4081617510789 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-151490709/1000000000 : ℝ), (6266937327/10000000000 : ℝ), (3942648053/10000000000 : ℝ)] ![(2584212568109/25000000000000 : ℝ), (44539226271/78125000000 : ℝ), (4081617510789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-151490709/1000000000 : ℝ)|^95 ≤ (2584212568109/25000000000000 : ℝ)^79
        have hw : |(-151490709/1000000000 : ℝ)|=(151490709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6266937327/10000000000 : ℝ)|^95 ≤ (44539226271/78125000000 : ℝ)^79
        have hw : |(6266937327/10000000000 : ℝ)|=(6266937327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3942648053/10000000000 : ℝ)|^95 ≤ (4081617510789/12500000000000 : ℝ)^79
        have hw : |(3942648053/10000000000 : ℝ)|=(3942648053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (518856849/625000000 : ℝ)*x 0 + (-1981/1250000000 : ℝ)*x 1 + (2628608869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518856849/625000000 : ℝ)^95 ≤ (79945938414997/100000000000000 : ℝ)^79 := by
    have hnat : (518856849 : ℕ)^95*100000000000000^79 ≤ 79945938414997^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518856849 625000000 79945938414997 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981/1250000000 : ℝ)^95 ≤ (10599509/100000000000000 : ℝ)^79 := by
    have hnat : (1981 : ℕ)^95*100000000000000^79 ≤ 10599509^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981 1250000000 10599509 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628608869/10000000000 : ℝ)^95 ≤ (10027025486387/50000000000000 : ℝ)^79 := by
    have hnat : (2628608869 : ℕ)^95*50000000000000^79 ≤ 10027025486387^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628608869 10000000000 10027025486387 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518856849/625000000 : ℝ), (-1981/1250000000 : ℝ), (2628608869/10000000000 : ℝ)] ![(79945938414997/100000000000000 : ℝ), (10599509/100000000000000 : ℝ), (10027025486387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518856849/625000000 : ℝ)|^95 ≤ (79945938414997/100000000000000 : ℝ)^79
        have hw : |(518856849/625000000 : ℝ)|=(518856849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981/1250000000 : ℝ)|^95 ≤ (10599509/100000000000000 : ℝ)^79
        have hw : |(-1981/1250000000 : ℝ)|=(1981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628608869/10000000000 : ℝ)|^95 ≤ (10027025486387/50000000000000 : ℝ)^79
        have hw : |(2628608869/10000000000 : ℝ)|=(2628608869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (893142811/10000000000 : ℝ)*x 0 + (159814359/200000000 : ℝ)*x 1 + (-242110107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893142811/10000000000 : ℝ)^95 ≤ (5475820355267/100000000000000 : ℝ)^79 := by
    have hnat : (893142811 : ℕ)^95*100000000000000^79 ≤ 5475820355267^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893142811 10000000000 5475820355267 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159814359/200000000 : ℝ)^95 ≤ (76358316300829/100000000000000 : ℝ)^79 := by
    have hnat : (159814359 : ℕ)^95*100000000000000^79 ≤ 76358316300829^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159814359 200000000 76358316300829 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242110107/1000000000 : ℝ)^95 ≤ (4541465833991/25000000000000 : ℝ)^79 := by
    have hnat : (242110107 : ℕ)^95*25000000000000^79 ≤ 4541465833991^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242110107 1000000000 4541465833991 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893142811/10000000000 : ℝ), (159814359/200000000 : ℝ), (-242110107/1000000000 : ℝ)] ![(5475820355267/100000000000000 : ℝ), (76358316300829/100000000000000 : ℝ), (4541465833991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893142811/10000000000 : ℝ)|^95 ≤ (5475820355267/100000000000000 : ℝ)^79
        have hw : |(893142811/10000000000 : ℝ)|=(893142811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(159814359/200000000 : ℝ)|^95 ≤ (76358316300829/100000000000000 : ℝ)^79
        have hw : |(159814359/200000000 : ℝ)|=(159814359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-242110107/1000000000 : ℝ)|^95 ≤ (4541465833991/25000000000000 : ℝ)^79
        have hw : |(-242110107/1000000000 : ℝ)|=(242110107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_25 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13/10000000000 : ℝ)*x 0 + (9999999999/10000000000 : ℝ)*x 1 + (13/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13/10000000000 : ℝ)^95 ≤ (1031/50000000000000 : ℝ)^79 := by
    have hnat : (13 : ℕ)^95*50000000000000^79 ≤ 1031^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13 10000000000 1031 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999999/10000000000 : ℝ)^95 ≤ (3999999999519/4000000000000 : ℝ)^79 := by
    have hnat : (9999999999 : ℕ)^95*4000000000000^79 ≤ 3999999999519^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 3999999999519 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13/10000000000 : ℝ)^95 ≤ (1031/50000000000000 : ℝ)^79 := by
    have hnat : (13 : ℕ)^95*50000000000000^79 ≤ 1031^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13 10000000000 1031 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13/10000000000 : ℝ), (9999999999/10000000000 : ℝ), (13/10000000000 : ℝ)] ![(1031/50000000000000 : ℝ), (3999999999519/4000000000000 : ℝ), (1031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13/10000000000 : ℝ)|^95 ≤ (1031/50000000000000 : ℝ)^79
        have hw : |(-13/10000000000 : ℝ)|=(13/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9999999999/10000000000 : ℝ)|^95 ≤ (3999999999519/4000000000000 : ℝ)^79
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13/10000000000 : ℝ)|^95 ≤ (1031/50000000000000 : ℝ)^79
        have hw : |(13/10000000000 : ℝ)|=(13/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6407864187/10000000000 : ℝ)*x 0 + (3008484141/10000000000 : ℝ)*x 1 + (2386747323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6407864187/10000000000 : ℝ)^95 ≤ (58555355861039/100000000000000 : ℝ)^79 := by
    have hnat : (6407864187 : ℕ)^95*100000000000000^79 ≤ 58555355861039^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6407864187 10000000000 58555355861039 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008484141/10000000000 : ℝ)^95 ≤ (23035448717/97656250000 : ℝ)^79 := by
    have hnat : (3008484141 : ℕ)^95*97656250000^79 ≤ 23035448717^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008484141 10000000000 23035448717 97656250000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386747323/10000000000 : ℝ)^95 ≤ (17856344634553/100000000000000 : ℝ)^79 := by
    have hnat : (2386747323 : ℕ)^95*100000000000000^79 ≤ 17856344634553^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386747323 10000000000 17856344634553 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6407864187/10000000000 : ℝ), (3008484141/10000000000 : ℝ), (2386747323/10000000000 : ℝ)] ![(58555355861039/100000000000000 : ℝ), (23035448717/97656250000 : ℝ), (17856344634553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6407864187/10000000000 : ℝ)|^95 ≤ (58555355861039/100000000000000 : ℝ)^79
        have hw : |(6407864187/10000000000 : ℝ)|=(6407864187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008484141/10000000000 : ℝ)|^95 ≤ (23035448717/97656250000 : ℝ)^79
        have hw : |(3008484141/10000000000 : ℝ)|=(3008484141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386747323/10000000000 : ℝ)|^95 ≤ (17856344634553/100000000000000 : ℝ)^79
        have hw : |(2386747323/10000000000 : ℝ)|=(2386747323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-661458257/2000000000 : ℝ)*x 0 + (5175189839/10000000000 : ℝ)*x 1 + (174908307/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661458257/2000000000 : ℝ)^95 ≤ (3304155084947/12500000000000 : ℝ)^79 := by
    have hnat : (661458257 : ℕ)^95*12500000000000^79 ≤ 3304155084947^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661458257 2000000000 3304155084947 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175189839/10000000000 : ℝ)^95 ≤ (45288434158777/100000000000000 : ℝ)^79 := by
    have hnat : (5175189839 : ℕ)^95*100000000000000^79 ≤ 45288434158777^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175189839 10000000000 45288434158777 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174908307/500000000 : ℝ)^95 ≤ (7069581287579/25000000000000 : ℝ)^79 := by
    have hnat : (174908307 : ℕ)^95*25000000000000^79 ≤ 7069581287579^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174908307 500000000 7069581287579 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-661458257/2000000000 : ℝ), (5175189839/10000000000 : ℝ), (174908307/500000000 : ℝ)] ![(3304155084947/12500000000000 : ℝ), (45288434158777/100000000000000 : ℝ), (7069581287579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-661458257/2000000000 : ℝ)|^95 ≤ (3304155084947/12500000000000 : ℝ)^79
        have hw : |(-661458257/2000000000 : ℝ)|=(661458257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175189839/10000000000 : ℝ)|^95 ≤ (45288434158777/100000000000000 : ℝ)^79
        have hw : |(5175189839/10000000000 : ℝ)|=(5175189839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(174908307/500000000 : ℝ)|^95 ≤ (7069581287579/25000000000000 : ℝ)^79
        have hw : |(174908307/500000000 : ℝ)|=(174908307/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1375349987/2500000000 : ℝ)*x 0 + (-468603981/5000000000 : ℝ)*x 1 + (1297749913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375349987/2500000000 : ℝ)^95 ≤ (24371420182083/50000000000000 : ℝ)^79 := by
    have hnat : (1375349987 : ℕ)^95*50000000000000^79 ≤ 24371420182083^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375349987 2500000000 24371420182083 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468603981/5000000000 : ℝ)^95 ≤ (5802300491607/100000000000000 : ℝ)^79 := by
    have hnat : (468603981 : ℕ)^95*100000000000000^79 ≤ 5802300491607^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468603981 5000000000 5802300491607 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297749913/2500000000 : ℝ)^95 ≤ (11363714782479/25000000000000 : ℝ)^79 := by
    have hnat : (1297749913 : ℕ)^95*25000000000000^79 ≤ 11363714782479^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297749913 2500000000 11363714782479 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375349987/2500000000 : ℝ), (-468603981/5000000000 : ℝ), (1297749913/2500000000 : ℝ)] ![(24371420182083/50000000000000 : ℝ), (5802300491607/100000000000000 : ℝ), (11363714782479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375349987/2500000000 : ℝ)|^95 ≤ (24371420182083/50000000000000 : ℝ)^79
        have hw : |(1375349987/2500000000 : ℝ)|=(1375349987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468603981/5000000000 : ℝ)|^95 ≤ (5802300491607/100000000000000 : ℝ)^79
        have hw : |(-468603981/5000000000 : ℝ)|=(468603981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297749913/2500000000 : ℝ)|^95 ≤ (11363714782479/25000000000000 : ℝ)^79
        have hw : |(1297749913/2500000000 : ℝ)|=(1297749913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3131437449/10000000000 : ℝ)*x 0 + (5503724549/10000000000 : ℝ)*x 1 + (-331216319/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3131437449/10000000000 : ℝ)^95 ≤ (24752318866429/100000000000000 : ℝ)^79 := by
    have hnat : (3131437449 : ℕ)^95*100000000000000^79 ≤ 24752318866429^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3131437449 10000000000 24752318866429 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503724549/10000000000 : ℝ)^95 ≤ (12191902236329/25000000000000 : ℝ)^79 := by
    have hnat : (5503724549 : ℕ)^95*25000000000000^79 ≤ 12191902236329^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503724549 10000000000 12191902236329 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (331216319/1000000000 : ℝ)^95 ≤ (13240036088459/50000000000000 : ℝ)^79 := by
    have hnat : (331216319 : ℕ)^95*50000000000000^79 ≤ 13240036088459^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331216319 1000000000 13240036088459 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3131437449/10000000000 : ℝ), (5503724549/10000000000 : ℝ), (-331216319/1000000000 : ℝ)] ![(24752318866429/100000000000000 : ℝ), (12191902236329/25000000000000 : ℝ), (13240036088459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3131437449/10000000000 : ℝ)|^95 ≤ (24752318866429/100000000000000 : ℝ)^79
        have hw : |(3131437449/10000000000 : ℝ)|=(3131437449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503724549/10000000000 : ℝ)|^95 ≤ (12191902236329/25000000000000 : ℝ)^79
        have hw : |(5503724549/10000000000 : ℝ)|=(5503724549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-331216319/1000000000 : ℝ)|^95 ≤ (13240036088459/50000000000000 : ℝ)^79
        have hw : |(-331216319/1000000000 : ℝ)|=(331216319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329031_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1851747953/5000000000 : ℝ)*x 0 + (4809764541/10000000000 : ℝ)*x 1 + (873634263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851747953/5000000000 : ℝ)^95 ≤ (6057202828731/20000000000000 : ℝ)^79 := by
    have hnat : (1851747953 : ℕ)^95*20000000000000^79 ≤ 6057202828731^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851747953 5000000000 6057202828731 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4809764541/10000000000 : ℝ)^95 ≤ (20735467627277/50000000000000 : ℝ)^79 := by
    have hnat : (4809764541 : ℕ)^95*50000000000000^79 ≤ 20735467627277^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809764541 10000000000 20735467627277 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873634263/2500000000 : ℝ)^95 ≤ (28243050588697/100000000000000 : ℝ)^79 := by
    have hnat : (873634263 : ℕ)^95*100000000000000^79 ≤ 28243050588697^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873634263 2500000000 28243050588697 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1851747953/5000000000 : ℝ), (4809764541/10000000000 : ℝ), (873634263/2500000000 : ℝ)] ![(6057202828731/20000000000000 : ℝ), (20735467627277/50000000000000 : ℝ), (28243050588697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1851747953/5000000000 : ℝ)|^95 ≤ (6057202828731/20000000000000 : ℝ)^79
        have hw : |(1851747953/5000000000 : ℝ)|=(1851747953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4809764541/10000000000 : ℝ)|^95 ≤ (20735467627277/50000000000000 : ℝ)^79
        have hw : |(4809764541/10000000000 : ℝ)|=(4809764541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873634263/2500000000 : ℝ)|^95 ≤ (28243050588697/100000000000000 : ℝ)^79
        have hw : |(873634263/2500000000 : ℝ)|=(873634263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329031 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-125470709/400000000 : ℝ)*X 0 0+(5189786851/10000000000 : ℝ)*X 0 1+(3649409007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3135424529/5000000000 : ℝ)*X 1 0+(618962941/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2598847661/10000000000 : ℝ)*X 2 0+(6176459627/10000000000 : ℝ)*X 2 1+(-3072881567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-696992369/2000000000 : ℝ)*X 0 0+(233555559/1000000000 : ℝ)*X 0 1+(3016147373/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4871486167/10000000000 : ℝ)*X 1 0+(507/2000000000 : ℝ)*X 1 1+(6347099941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((226207899/2000000000 : ℝ)*X 2 0+(1023760613/1250000000 : ℝ)*X 2 1+(-1957772827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2250050693/10000000000 : ℝ)*X 0 0+(6584419081/10000000000 : ℝ)*X 0 1+(2931609807/10000000000 : ℝ)*X 0 2+(2250050693/10000000000 : ℝ)*X 1 0+(6584419081/10000000000 : ℝ)*X 1 1+(2931609807/10000000000 : ℝ)*X 1 2+(2250050693/10000000000 : ℝ)*X 2 0+(6584419081/10000000000 : ℝ)*X 2 1+(2931609807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4152370249/10000000000 : ℝ)*X 0 0+(1510232819/5000000000 : ℝ)*X 0 1+(963399759/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1030705537/1250000000 : ℝ)*X 1 0+(6149/1000000000 : ℝ)*X 1 1+(1349567489/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((224234771/2500000000 : ℝ)*X 2 0+(134351279/200000000 : ℝ)*X 2 1+(-3929410817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2079676449/10000000000 : ℝ)*X 0 0+(1082220353/2500000000 : ℝ)*X 0 1+(5462830777/10000000000 : ℝ)*X 0 2+(2079676449/10000000000 : ℝ)*X 1 0+(1082220353/2500000000 : ℝ)*X 1 1+(5462830777/10000000000 : ℝ)*X 1 2+(2079676449/10000000000 : ℝ)*X 2 0+(1082220353/2500000000 : ℝ)*X 2 1+(5462830777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-151490709/1000000000 : ℝ)*X 0 0+(6266937327/10000000000 : ℝ)*X 0 1+(3942648053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((518856849/625000000 : ℝ)*X 1 0+(-1981/1250000000 : ℝ)*X 1 1+(2628608869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((893142811/10000000000 : ℝ)*X 2 0+(159814359/200000000 : ℝ)*X 2 1+(-242110107/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((-13/10000000000 : ℝ)*X 0 0+(9999999999/10000000000 : ℝ)*X 0 1+(13/10000000000 : ℝ)*X 0 2+(-13/10000000000 : ℝ)*X 2 0+(9999999999/10000000000 : ℝ)*X 2 1+(13/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_25 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6407864187/10000000000 : ℝ)*X 0 0+(3008484141/10000000000 : ℝ)*X 0 1+(2386747323/10000000000 : ℝ)*X 0 2+(6407864187/10000000000 : ℝ)*X 1 0+(3008484141/10000000000 : ℝ)*X 1 1+(2386747323/10000000000 : ℝ)*X 1 2+(6407864187/10000000000 : ℝ)*X 2 0+(3008484141/10000000000 : ℝ)*X 2 1+(2386747323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((13213/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13213/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23329112254249124836467/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1239848463273/1000000000000 : ℝ)*(base7) + (1358771541/10000000000 : ℝ)*(base50) + (1862107/250000000000 : ℝ)*(base53) + (9504986021/250000000000 : ℝ)*(base60) + (1653366045601/1000000000000 : ℝ)*(major_s0_0) + (517477026383/200000000000 : ℝ)*(major_s0_1) + (1653358597173/1000000000000 : ℝ)*(major_s0_2) + (42351301/1000000000000 : ℝ)*(sp_s0_0) + (1900794326641/1000000000000 : ℝ)*(sp_s0_7) + (950418338971/500000000000 : ℝ)*(sp_s0_8) + (237593668221/125000000000 : ℝ)*(sp_s0_9) + (495853889101/250000000000 : ℝ)*(sp_s0_13) + (94780601/1000000000000 : ℝ)*(sp_s0_23) + (467009543157/500000000000 : ℝ)*(sp_s0_25) + (74356709313/100000000000 : ℝ)*(f.failure) + (1900844126369/1000000000000 : ℝ)*(f.sum) + (1500951973985747/5000000000000000000000000000 : ℝ)*base62 + (866563896588573/10000000000000000000000000000 : ℝ)*base64 + (1625114978795783/2000000000000000000000000000 : ℝ)*base66 + (2623875380091661/10000000000000000000000000000 : ℝ)*base69 + (792069047078929/2500000000000000000000000000 : ℝ)*base70 + (3610773837087401/10000000000000000000000000000 : ℝ)*base72 + (395737011012631/2000000000000000000000000000 : ℝ)*base74 + (4164108019272857/10000000000000000000000000000 : ℝ)*base77 + (1387551945516579/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (2143/2500000000000000 : ℝ)*base86 + (2143/2500000000000000 : ℝ)*base88 + (2143/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13633/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(13633/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3103659070175288900493/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7369111/500000000000 : ℝ)*(base3) + (65055917851/125000000000 : ℝ)*(base7) + (496197053463/1000000000000 : ℝ)*(base40) + (18343457189/62500000000 : ℝ)*(base60) + (211328902639/125000000000 : ℝ)*(major_s0_0) + (211328902639/125000000000 : ℝ)*(major_s0_1) + (211328902639/125000000000 : ℝ)*(major_s0_2) + (20431/1250000000 : ℝ)*(sp_s0_1) + (18769447/500000000000 : ℝ)*(sp_s0_2) + (29687883/500000000000 : ℝ)*(sp_s0_7) + (1171427828391/500000000000 : ℝ)*(sp_s0_14) + (234291342597/100000000000 : ℝ)*(sp_s0_15) + (1171438746827/500000000000 : ℝ)*(sp_s0_16) + (256151787527/200000000000 : ℝ)*(sp_s0_20) + (95040791631/125000000000 : ℝ)*(f.failure) + (585728758137/250000000000 : ℝ)*(f.sum) + (3809731127/10000000000000000000000 : ℝ)*base62 + (172433910407161/1250000000000000000000000000 : ℝ)*base65 + (108499345217839/1250000000000000000000000000 : ℝ)*base66 + (634352737534177/1250000000000000000000000000 : ℝ)*base68 + (25879167390751/78125000000000000000000000 : ℝ)*base70 + (372009413032161/1250000000000000000000000000 : ℝ)*base73 + (74832464965823/1250000000000000000000000000 : ℝ)*base74 + (623718090409177/1250000000000000000000000000 : ℝ)*base76 + (129901958719661/625000000000000000000000000 : ℝ)*base79 + (659/3125000000000000 : ℝ)*base87 + (659/3125000000000000 : ℝ)*base89 + (659/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14247/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14247/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13039844057996534426439/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1257428128389/1000000000000 : ℝ)*(base7) + (254793/125000000000 : ℝ)*(base11) + (25633337101/100000000000 : ℝ)*(base40) + (3099513831/1000000000000 : ℝ)*(base50) + (1676387844913/1000000000000 : ℝ)*(major_s0_0) + (1676389132003/1000000000000 : ℝ)*(major_s0_1) + (1676387844913/1000000000000 : ℝ)*(major_s0_2) + (2810073/500000000000 : ℝ)*(sp_s0_2) + (48677509/1000000000000 : ℝ)*(sp_s0_9) + (1927145710957/1000000000000 : ℝ)*(sp_s0_21) + (1927147749301/1000000000000 : ℝ)*(sp_s0_22) + (963546725823/500000000000 : ℝ)*(sp_s0_23) + (1287091/1000000000000 : ℝ)*(sp_s0_25) + (502837199589/250000000000 : ℝ)*(sp_s0_27) + (753920669967/1000000000000 : ℝ)*(f.failure) + (1927147749301/1000000000000 : ℝ)*(f.sum) + (476799732178813/1000000000000000000000000000 : ℝ)*base62 + (3481853575168313/10000000000000000000000000000 : ℝ)*base64 + (1313522927617403/10000000000000000000000000000 : ℝ)*base66 + (6404793456476841/10000000000000000000000000000 : ℝ)*base69 + (116665270831783/625000000000000000000000000 : ℝ)*base71 + (2878971911831687/10000000000000000000000000000 : ℝ)*base73 + (1345466631264971/10000000000000000000000000000 : ℝ)*base74 + (1630229670523159/10000000000000000000000000000 : ℝ)*base76 + (1873356198196429/2500000000000000000000000000 : ℝ)*base78 + (29437/25000000000000000 : ℝ)*base86 + (4437/25000000000000000 : ℝ)*base88 + (29437/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (13213/25000 : ℝ) ^ (93/16 : ℝ) ≤ (1228187137488039829/50000000000000000000 : ℝ) := by
    have hpowers : (13213/25000 : ℝ)^93 ≤ (1228187137488039829/50000000000000000000 : ℝ)^16 := by
      have hnat : (13213 : ℕ)^93*50000000000000000000^16 ≤ 1228187137488039829^16*25000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13213 25000 1228187137488039829 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13213/25000 : ℝ)) (X := (1228187137488039829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51228187137488039829/50000000000000000000 : ℝ) ≤ (1255229598345237/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (51228187137488039829/50000000000000000000 : ℝ)^16 ≤ (1255229598345237/1250000000000000 : ℝ)^93 := by
      have hnat : (51228187137488039829 : ℕ)^16*1250000000000000^93 ≤ 1255229598345237^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51228187137488039829 50000000000000000000 1255229598345237 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255229598345237/1250000000000000 : ℝ)) (X := (51228187137488039829/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26228187137488039829/25000000000000000000 : ℝ) ≤ (315089099554723/312500000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (26228187137488039829/25000000000000000000 : ℝ)^16 ≤ (315089099554723/312500000000000 : ℝ)^93 := by
      have hnat : (26228187137488039829 : ℕ)^16*312500000000000^93 ≤ 315089099554723^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26228187137488039829 25000000000000000000 315089099554723 312500000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315089099554723/312500000000000 : ℝ)) (X := (26228187137488039829/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5229598345237/660650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1025359974731/132130000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (13213/25000 : ℝ)) (alpha := (5229598345237/660650000000000 : ℝ)) (beta := (1025359974731/132130000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13213/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5229598345237/660650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1025359974731/132130000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (13633/50000 : ℝ) ^ (93/16 : ℝ) ≤ (52426342939505107/100000000000000000000 : ℝ) := by
    have hpowers : (13633/50000 : ℝ)^93 ≤ (52426342939505107/100000000000000000000 : ℝ)^16 := by
      have hnat : (13633 : ℕ)^93*100000000000000000000^16 ≤ 52426342939505107^16*50000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13633 50000 52426342939505107 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13633/50000 : ℝ)) (X := (52426342939505107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100052426342939505107/100000000000000000000 : ℝ) ≤ (1000090176289523/1000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (100052426342939505107/100000000000000000000 : ℝ)^16 ≤ (1000090176289523/1000000000000000 : ℝ)^93 := by
      have hnat : (100052426342939505107 : ℕ)^16*1000000000000000^93 ≤ 1000090176289523^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052426342939505107 100000000000000000000 1000090176289523 1000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000090176289523/1000000000000000 : ℝ)) (X := (100052426342939505107/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50052426342939505107/50000000000000000000 : ℝ) ≤ (250045078366359/250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (50052426342939505107/50000000000000000000 : ℝ)^16 ≤ (250045078366359/250000000000000 : ℝ)^93 := by
      have hnat : (50052426342939505107 : ℕ)^16*250000000000000^93 ≤ 250045078366359^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50052426342939505107 50000000000000000000 250045078366359 250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250045078366359/250000000000000 : ℝ)) (X := (50052426342939505107/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(90176289523/272660000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(90137175913/272660000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (13633/50000 : ℝ)) (alpha := (90176289523/272660000000000 : ℝ)) (beta := (90137175913/272660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (13633/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(90176289523/272660000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(90137175913/272660000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (14247/25000 : ℝ) ^ (93/16 : ℝ) ≤ (380619560415505979/10000000000000000000 : ℝ) := by
    have hpowers : (14247/25000 : ℝ)^93 ≤ (380619560415505979/10000000000000000000 : ℝ)^16 := by
      have hnat : (14247 : ℕ)^93*10000000000000000000^16 ≤ 380619560415505979^16*25000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14247 25000 380619560415505979 10000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14247/25000 : ℝ)) (X := (380619560415505979/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10380619560415505979/10000000000000000000 : ℝ) ≤ (314514826103203/312500000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (10380619560415505979/10000000000000000000 : ℝ)^16 ≤ (314514826103203/312500000000000 : ℝ)^93 := by
      have hnat : (10380619560415505979 : ℕ)^16*312500000000000^93 ≤ 314514826103203^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10380619560415505979 10000000000000000000 314514826103203 312500000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314514826103203/312500000000000 : ℝ)) (X := (10380619560415505979/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5380619560415505979/5000000000000000000 : ℝ) ≤ (10127020354690041/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (5380619560415505979/5000000000000000000 : ℝ)^16 ≤ (10127020354690041/10000000000000000 : ℝ)^93 := by
      have hnat : (5380619560415505979 : ℕ)^16*10000000000000000^93 ≤ 10127020354690041^93*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5380619560415505979 5000000000000000000 10127020354690041 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10127020354690041/10000000000000000 : ℝ)) (X := (5380619560415505979/5000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(2014826103203/178087500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12509183877509/1139760000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (14247/25000 : ℝ)) (alpha := (2014826103203/178087500000000 : ℝ)) (beta := (12509183877509/1139760000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14247/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(2014826103203/178087500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12509183877509/1139760000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-661458257/2000000000 : ℝ)*X 0 0+(5175189839/10000000000 : ℝ)*X 0 1+(174908307/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1375349987/2500000000 : ℝ)*X 1 0+(-468603981/5000000000 : ℝ)*X 1 1+(1297749913/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3131437449/10000000000 : ℝ)*X 2 0+(5503724549/10000000000 : ℝ)*X 2 1+(-331216319/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1851747953/5000000000 : ℝ)*X 0 0+(4809764541/10000000000 : ℝ)*X 0 1+(873634263/2500000000 : ℝ)*X 0 2+(1851747953/5000000000 : ℝ)*X 1 0+(4809764541/10000000000 : ℝ)*X 1 1+(873634263/2500000000 : ℝ)*X 1 2+(1851747953/5000000000 : ℝ)*X 2 0+(4809764541/10000000000 : ℝ)*X 2 1+(873634263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329031_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-18451062194255400395893202060289/1801328290000000000000000000000 : ℝ) := by norm_num
    linear_combination (91/200000000000 : ℝ)*(base15) + (4447/1000000000000 : ℝ)*(base16) + (7223/250000000000 : ℝ)*(base23) + (118975903839/1000000000000 : ℝ)*(base40) + (5751/1000000000000 : ℝ)*(base43) + (102847438379/1000000000000 : ℝ)*(base49) + (783294625277/1000000000000 : ℝ)*(base50) + (1057/250000000000 : ℝ)*(base60) + (55589/25000 : ℝ)*(major_s1_0) + (2223559994249/1000000000000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (426792973311/125000000000 : ℝ)*(sp_s1_0) + (426792973417/125000000000 : ℝ)*(sp_s1_1) + (853585939399/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (3414343792239/1000000000000 : ℝ)*(f.sum) + (78556206143714909/3884587020000000000000000000000 : ℝ)*base62 + (5378918047537/17808750000000000000000000 : ℝ)*base65 + (42463916256783/272660000000000000000000000 : ℝ)*base66 + (77079385987/4452187500000000000000000 : ℝ)*base69 + (44747608427122453/117653506875000000000000000000 : ℝ)*base70 + (1799583517427/4129062500000000000000000 : ℝ)*base73 + (111120385786109/272660000000000000000000000 : ℝ)*base75 + (16024747751863/33032500000000000000000000 : ℝ)*base76 + (70556364030899299/3602656580000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c329032_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2484940531/10000000000 : ℝ)*x 0 + (-2073999437/5000000000 : ℝ)*x 1 + (-5294590769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2484940531/10000000000 : ℝ)^95 ≤ (2342924895613/12500000000000 : ℝ)^79 := by
    have hnat : (2484940531 : ℕ)^95*12500000000000^79 ≤ 2342924895613^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2484940531 10000000000 2342924895613 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073999437/5000000000 : ℝ)^95 ≤ (17354370419287/50000000000000 : ℝ)^79 := by
    have hnat : (2073999437 : ℕ)^95*50000000000000^79 ≤ 17354370419287^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073999437 5000000000 17354370419287 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5294590769/10000000000 : ℝ)^95 ≤ (46547859981641/100000000000000 : ℝ)^79 := by
    have hnat : (5294590769 : ℕ)^95*100000000000000^79 ≤ 46547859981641^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294590769 10000000000 46547859981641 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2484940531/10000000000 : ℝ), (-2073999437/5000000000 : ℝ), (-5294590769/10000000000 : ℝ)] ![(2342924895613/12500000000000 : ℝ), (17354370419287/50000000000000 : ℝ), (46547859981641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2484940531/10000000000 : ℝ)|^95 ≤ (2342924895613/12500000000000 : ℝ)^79
        have hw : |(-2484940531/10000000000 : ℝ)|=(2484940531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073999437/5000000000 : ℝ)|^95 ≤ (17354370419287/50000000000000 : ℝ)^79
        have hw : |(-2073999437/5000000000 : ℝ)|=(2073999437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5294590769/10000000000 : ℝ)|^95 ≤ (46547859981641/100000000000000 : ℝ)^79
        have hw : |(-5294590769/10000000000 : ℝ)|=(5294590769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329032_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (569583487/2000000000 : ℝ)*x 0 + (314214811/625000000 : ℝ)*x 1 + (-4095306157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (569583487/2000000000 : ℝ)^95 ≤ (2208268766717/10000000000000 : ℝ)^79 := by
    have hnat : (569583487 : ℕ)^95*10000000000000^79 ≤ 2208268766717^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569583487 2000000000 2208268766717 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314214811/625000000 : ℝ)^95 ≤ (21869048203333/50000000000000 : ℝ)^79 := by
    have hnat : (314214811 : ℕ)^95*50000000000000^79 ≤ 21869048203333^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314214811 625000000 21869048203333 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4095306157/10000000000 : ℝ)^95 ≤ (8544803980289/25000000000000 : ℝ)^79 := by
    have hnat : (4095306157 : ℕ)^95*25000000000000^79 ≤ 8544803980289^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4095306157 10000000000 8544803980289 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(569583487/2000000000 : ℝ), (314214811/625000000 : ℝ), (-4095306157/10000000000 : ℝ)] ![(2208268766717/10000000000000 : ℝ), (21869048203333/50000000000000 : ℝ), (8544803980289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(569583487/2000000000 : ℝ)|^95 ≤ (2208268766717/10000000000000 : ℝ)^79
        have hw : |(569583487/2000000000 : ℝ)|=(569583487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314214811/625000000 : ℝ)|^95 ≤ (21869048203333/50000000000000 : ℝ)^79
        have hw : |(314214811/625000000 : ℝ)|=(314214811/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4095306157/10000000000 : ℝ)|^95 ≤ (8544803980289/25000000000000 : ℝ)^79
        have hw : |(-4095306157/10000000000 : ℝ)|=(4095306157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329032_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6688729059/10000000000 : ℝ)*x 0 + (-1393959087/5000000000 : ℝ)*x 1 + (2271013743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6688729059/10000000000 : ℝ)^95 ≤ (61655263344497/100000000000000 : ℝ)^79 := by
    have hnat : (6688729059 : ℕ)^95*100000000000000^79 ≤ 61655263344497^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6688729059 10000000000 61655263344497 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393959087/5000000000 : ℝ)^95 ≤ (10762215339671/50000000000000 : ℝ)^79 := by
    have hnat : (1393959087 : ℕ)^95*50000000000000^79 ≤ 10762215339671^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393959087 5000000000 10762215339671 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271013743/10000000000 : ℝ)^95 ≤ (8410152982367/50000000000000 : ℝ)^79 := by
    have hnat : (2271013743 : ℕ)^95*50000000000000^79 ≤ 8410152982367^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271013743 10000000000 8410152982367 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6688729059/10000000000 : ℝ), (-1393959087/5000000000 : ℝ), (2271013743/10000000000 : ℝ)] ![(61655263344497/100000000000000 : ℝ), (10762215339671/50000000000000 : ℝ), (8410152982367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6688729059/10000000000 : ℝ)|^95 ≤ (61655263344497/100000000000000 : ℝ)^79
        have hw : |(6688729059/10000000000 : ℝ)|=(6688729059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1393959087/5000000000 : ℝ)|^95 ≤ (10762215339671/50000000000000 : ℝ)^79
        have hw : |(-1393959087/5000000000 : ℝ)|=(1393959087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271013743/10000000000 : ℝ)|^95 ≤ (8410152982367/50000000000000 : ℝ)^79
        have hw : |(2271013743/10000000000 : ℝ)|=(2271013743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329032_s0_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1764041989/5000000000 : ℝ)*x 0 + (-3726417419/10000000000 : ℝ)*x 1 + (-118911889/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1764041989/5000000000 : ℝ)^95 ≤ (1785587935887/6250000000000 : ℝ)^79 := by
    have hnat : (1764041989 : ℕ)^95*6250000000000^79 ≤ 1785587935887^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764041989 5000000000 1785587935887 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726417419/10000000000 : ℝ)^95 ≤ (30511563560983/100000000000000 : ℝ)^79 := by
    have hnat : (3726417419 : ℕ)^95*100000000000000^79 ≤ 30511563560983^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726417419 10000000000 30511563560983 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118911889/250000000 : ℝ)^95 ≤ (20459514722491/50000000000000 : ℝ)^79 := by
    have hnat : (118911889 : ℕ)^95*50000000000000^79 ≤ 20459514722491^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118911889 250000000 20459514722491 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1764041989/5000000000 : ℝ), (-3726417419/10000000000 : ℝ), (-118911889/250000000 : ℝ)] ![(1785587935887/6250000000000 : ℝ), (30511563560983/100000000000000 : ℝ), (20459514722491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1764041989/5000000000 : ℝ)|^95 ≤ (1785587935887/6250000000000 : ℝ)^79
        have hw : |(1764041989/5000000000 : ℝ)|=(1764041989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3726417419/10000000000 : ℝ)|^95 ≤ (30511563560983/100000000000000 : ℝ)^79
        have hw : |(-3726417419/10000000000 : ℝ)|=(3726417419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118911889/250000000 : ℝ)|^95 ≤ (20459514722491/50000000000000 : ℝ)^79
        have hw : |(-118911889/250000000 : ℝ)|=(118911889/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329032 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2484940531/10000000000 : ℝ)*X 0 0+(-2073999437/5000000000 : ℝ)*X 0 1+(-5294590769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329032_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((569583487/2000000000 : ℝ)*X 1 0+(314214811/625000000 : ℝ)*X 1 1+(-4095306157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329032_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6688729059/10000000000 : ℝ)*X 2 0+(-1393959087/5000000000 : ℝ)*X 2 1+(2271013743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329032_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1764041989/5000000000 : ℝ)*X 0 0+(-3726417419/10000000000 : ℝ)*X 0 1+(-118911889/250000000 : ℝ)*X 0 2+(1764041989/5000000000 : ℝ)*X 1 0+(-3726417419/10000000000 : ℝ)*X 1 1+(-118911889/250000000 : ℝ)*X 1 2+(1764041989/5000000000 : ℝ)*X 2 0+(-3726417419/10000000000 : ℝ)*X 2 1+(-118911889/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329032_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-5108699258207091916842248511/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (329957/500000000000 : ℝ)*(base5) + (238573/500000000000 : ℝ)*(base12) + (79192832373/100000000000 : ℝ)*(base39) + (61978914921/100000000000 : ℝ)*(base40) + (31418870379/250000000000 : ℝ)*(base50) + (853/200000000000 : ℝ)*(base53) + (16013/62500000000 : ℝ)*(base59) + (619188120611/1000000000000 : ℝ)*(base60) + (55589/25000 : ℝ)*(major_s0_0) + (55589/25000 : ℝ)*(major_s0_1) + (444711999147/200000000000 : ℝ)*(major_s0_2) + (425724878007/125000000000 : ℝ)*(sp_s0_0) + (1702899750601/500000000000 : ℝ)*(sp_s0_1) + (3405800165381/1000000000000 : ℝ)*(sp_s0_2) + (499999670043/500000000000 : ℝ)*(sp_s0_6) + (3405799505467/1000000000000 : ℝ)*(f.sum) + (150260361749421/2000000000000000000000000000 : ℝ)*base63 + (690033498816253/2000000000000000000000000000 : ℝ)*base64 + (210245701/625000000000000000000 : ℝ)*base66 + (633294456549421/2000000000000000000000000000 : ℝ)*base69 + (2044233334016253/2000000000000000000000000000 : ℝ)*base70 + (4962283657/5000000000000000000000 : ℝ)*base73 + (5783089667/10000000000000000000000 : ℝ)*base74 + (251371797/625000000000000000000 : ℝ)*base76 + (3263467077/10000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b013 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 31 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=31 ∨ c=32 := by omega
  rcases hc with rfl|rfl
  · exact collision_c329031 p hpa (by linarith only [hpb]) X hX
  · exact collision_c329032 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 31 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b013 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
