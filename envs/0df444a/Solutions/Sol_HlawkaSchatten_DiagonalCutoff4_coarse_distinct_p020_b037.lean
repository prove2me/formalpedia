-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p020_b037
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:34:15.007211+00:00
-- url     : https://prove2.me/submissions/e1eeddc8-edad-47bf-9816-b488803e6d2c

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
theorem collision_support_c320070_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-53815649/250000000 : ℝ)*x 0 + (-394969153/1000000000 : ℝ)*x 1 + (-1520812503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53815649/250000000 : ℝ)^81 ≤ (589978538351/4000000000000 : ℝ)^65 := by
    have hnat : (53815649 : ℕ)^81*4000000000000^65 ≤ 589978538351^65*250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53815649 250000000 589978538351 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394969153/1000000000 : ℝ)^81 ≤ (7855894853961/25000000000000 : ℝ)^65 := by
    have hnat : (394969153 : ℕ)^81*25000000000000^65 ≤ 7855894853961^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394969153 1000000000 7855894853961 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1520812503/2500000000 : ℝ)^81 ≤ (26913478559919/50000000000000 : ℝ)^65 := by
    have hnat : (1520812503 : ℕ)^81*50000000000000^65 ≤ 26913478559919^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520812503 2500000000 26913478559919 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53815649/250000000 : ℝ), (-394969153/1000000000 : ℝ), (-1520812503/2500000000 : ℝ)] ![(589978538351/4000000000000 : ℝ), (7855894853961/25000000000000 : ℝ), (26913478559919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53815649/250000000 : ℝ)|^81 ≤ (589978538351/4000000000000 : ℝ)^65
        have hw : |(-53815649/250000000 : ℝ)|=(53815649/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-394969153/1000000000 : ℝ)|^81 ≤ (7855894853961/25000000000000 : ℝ)^65
        have hw : |(-394969153/1000000000 : ℝ)|=(394969153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1520812503/2500000000 : ℝ)|^81 ≤ (26913478559919/50000000000000 : ℝ)^65
        have hw : |(-1520812503/2500000000 : ℝ)|=(1520812503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320070_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (760406251/1250000000 : ℝ)*x 0 + (789938307/2000000000 : ℝ)*x 1 + (-1076312979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760406251/1250000000 : ℝ)^81 ≤ (13456739268933/25000000000000 : ℝ)^65 := by
    have hnat : (760406251 : ℕ)^81*25000000000000^65 ≤ 13456739268933^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760406251 1250000000 13456739268933 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (789938307/2000000000 : ℝ)^81 ≤ (3927947433177/12500000000000 : ℝ)^65 := by
    have hnat : (789938307 : ℕ)^81*12500000000000^65 ≤ 3927947433177^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789938307 2000000000 3927947433177 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076312979/5000000000 : ℝ)^81 ≤ (7374731720849/50000000000000 : ℝ)^65 := by
    have hnat : (1076312979 : ℕ)^81*50000000000000^65 ≤ 7374731720849^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076312979 5000000000 7374731720849 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(760406251/1250000000 : ℝ), (789938307/2000000000 : ℝ), (-1076312979/5000000000 : ℝ)] ![(13456739268933/25000000000000 : ℝ), (3927947433177/12500000000000 : ℝ), (7374731720849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(760406251/1250000000 : ℝ)|^81 ≤ (13456739268933/25000000000000 : ℝ)^65
        have hw : |(760406251/1250000000 : ℝ)|=(760406251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(789938307/2000000000 : ℝ)|^81 ≤ (3927947433177/12500000000000 : ℝ)^65
        have hw : |(789938307/2000000000 : ℝ)|=(789938307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076312979/5000000000 : ℝ)|^81 ≤ (7374731720849/50000000000000 : ℝ)^65
        have hw : |(-1076312979/5000000000 : ℝ)|=(1076312979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320070_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (370161577/1000000000 : ℝ)*x 0 + (-4988209699/10000000000 : ℝ)*x 1 + (3701615761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370161577/1000000000 : ℝ)^81 ≤ (28983391567933/100000000000000 : ℝ)^65 := by
    have hnat : (370161577 : ℕ)^81*100000000000000^65 ≤ 28983391567933^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370161577 1000000000 28983391567933 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988209699/10000000000 : ℝ)^81 ≤ (42033216936859/100000000000000 : ℝ)^65 := by
    have hnat : (4988209699 : ℕ)^81*100000000000000^65 ≤ 42033216936859^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988209699 10000000000 42033216936859 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3701615761/10000000000 : ℝ)^81 ≤ (14491695740059/50000000000000 : ℝ)^65 := by
    have hnat : (3701615761 : ℕ)^81*50000000000000^65 ≤ 14491695740059^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701615761 10000000000 14491695740059 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(370161577/1000000000 : ℝ), (-4988209699/10000000000 : ℝ), (3701615761/10000000000 : ℝ)] ![(28983391567933/100000000000000 : ℝ), (42033216936859/100000000000000 : ℝ), (14491695740059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(370161577/1000000000 : ℝ)|^81 ≤ (28983391567933/100000000000000 : ℝ)^65
        have hw : |(370161577/1000000000 : ℝ)|=(370161577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4988209699/10000000000 : ℝ)|^81 ≤ (42033216936859/100000000000000 : ℝ)^65
        have hw : |(-4988209699/10000000000 : ℝ)|=(4988209699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3701615761/10000000000 : ℝ)|^81 ≤ (14491695740059/50000000000000 : ℝ)^65
        have hw : |(3701615761/10000000000 : ℝ)|=(3701615761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320070_s0_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4957594917/10000000000 : ℝ)*x 0 + (-2364053563/10000000000 : ℝ)*x 1 + (-309849683/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4957594917/10000000000 : ℝ)^81 ≤ (20855991258551/50000000000000 : ℝ)^65 := by
    have hnat : (4957594917 : ℕ)^81*50000000000000^65 ≤ 20855991258551^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4957594917 10000000000 20855991258551 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2364053563/10000000000 : ℝ)^81 ≤ (4144008707791/25000000000000 : ℝ)^65 := by
    have hnat : (2364053563 : ℕ)^81*25000000000000^65 ≤ 4144008707791^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364053563 10000000000 4144008707791 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309849683/625000000 : ℝ)^81 ≤ (8342396526487/20000000000000 : ℝ)^65 := by
    have hnat : (309849683 : ℕ)^81*20000000000000^65 ≤ 8342396526487^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309849683 625000000 8342396526487 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4957594917/10000000000 : ℝ), (-2364053563/10000000000 : ℝ), (-309849683/625000000 : ℝ)] ![(20855991258551/50000000000000 : ℝ), (4144008707791/25000000000000 : ℝ), (8342396526487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4957594917/10000000000 : ℝ)|^81 ≤ (20855991258551/50000000000000 : ℝ)^65
        have hw : |(4957594917/10000000000 : ℝ)|=(4957594917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2364053563/10000000000 : ℝ)|^81 ≤ (4144008707791/25000000000000 : ℝ)^65
        have hw : |(-2364053563/10000000000 : ℝ)|=(2364053563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-309849683/625000000 : ℝ)|^81 ≤ (8342396526487/20000000000000 : ℝ)^65
        have hw : |(-309849683/625000000 : ℝ)|=(309849683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320070 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-53815649/250000000 : ℝ)*X 0 0+(-394969153/1000000000 : ℝ)*X 0 1+(-1520812503/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((760406251/1250000000 : ℝ)*X 1 0+(789938307/2000000000 : ℝ)*X 1 1+(-1076312979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((370161577/1000000000 : ℝ)*X 2 0+(-4988209699/10000000000 : ℝ)*X 2 1+(3701615761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4957594917/10000000000 : ℝ)*X 0 0+(-2364053563/10000000000 : ℝ)*X 0 1+(-309849683/625000000 : ℝ)*X 0 2+(4957594917/10000000000 : ℝ)*X 1 0+(-2364053563/10000000000 : ℝ)*X 1 1+(-309849683/625000000 : ℝ)*X 1 2+(4957594917/10000000000 : ℝ)*X 2 0+(-2364053563/10000000000 : ℝ)*X 2 1+(-309849683/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-10236574150566920808053886411/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (649/1000000000000 : ℝ)*(base3) + (3009/1000000000000 : ℝ)*(base33) + (611677198259/1000000000000 : ℝ)*(base39) + (10523/1000000000000 : ℝ)*(base43) + (37768246671/200000000000 : ℝ)*(base49) + (5043/1000000000000 : ℝ)*(base54) + (380476798941/1000000000000 : ℝ)*(base59) + (1877199996991/1000000000000 : ℝ)*(major_s0_0) + (1877199989477/1000000000000 : ℝ)*(major_s0_1) + (1877199994957/1000000000000 : ℝ)*(major_s0_2) + (682438273981/250000000000 : ℝ)*(sp_s0_0) + (272975310421/100000000000 : ℝ)*(sp_s0_1) + (1364876543997/500000000000 : ℝ)*(sp_s0_2) + (99999999443/100000000000 : ℝ)*(sp_s0_6) + (272975310657/100000000000 : ℝ)*(f.sum) + (109357922974229/625000000000000000000000000 : ℝ)*base62 + (681528900062389/10000000000000000000000000000 : ℝ)*base64 + (3908598733996427/10000000000000000000000000000 : ℝ)*base66 + (5781208709519907/10000000000000000000000000000 : ℝ)*base69 + (295579907712137/2500000000000000000000000000 : ℝ)*base70 + (1839401350132407/10000000000000000000000000000 : ℝ)*base72 + (1604766112892429/10000000000000000000000000000 : ℝ)*base75 + (897696764786159/10000000000000000000000000000 : ℝ)*base76 + (405120586935583/5000000000000000000000000000 : ℝ)*base79 + (123/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (61/500000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c320071_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3569067501/10000000000 : ℝ)*x 0 + (508655931/1000000000 : ℝ)*x 1 + (74549073/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3569067501/10000000000 : ℝ)^81 ≤ (3461978834653/12500000000000 : ℝ)^65 := by
    have hnat : (3569067501 : ℕ)^81*12500000000000^65 ≤ 3461978834653^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3569067501 10000000000 3461978834653 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508655931/1000000000 : ℝ)^81 ≤ (21534226829771/50000000000000 : ℝ)^65 := by
    have hnat : (508655931 : ℕ)^81*50000000000000^65 ≤ 21534226829771^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508655931 1000000000 21534226829771 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74549073/200000000 : ℝ)^81 ≤ (2923571564631/10000000000000 : ℝ)^65 := by
    have hnat : (74549073 : ℕ)^81*10000000000000^65 ≤ 2923571564631^65*200000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74549073 200000000 2923571564631 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3569067501/10000000000 : ℝ), (508655931/1000000000 : ℝ), (74549073/200000000 : ℝ)] ![(3461978834653/12500000000000 : ℝ), (21534226829771/50000000000000 : ℝ), (2923571564631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3569067501/10000000000 : ℝ)|^81 ≤ (3461978834653/12500000000000 : ℝ)^65
        have hw : |(3569067501/10000000000 : ℝ)|=(3569067501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508655931/1000000000 : ℝ)|^81 ≤ (21534226829771/50000000000000 : ℝ)^65
        have hw : |(508655931/1000000000 : ℝ)|=(508655931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74549073/200000000 : ℝ)|^81 ≤ (2923571564631/10000000000000 : ℝ)^65
        have hw : |(74549073/200000000 : ℝ)|=(74549073/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1886036849/5000000000 : ℝ)*x 0 + (-5014936607/10000000000 : ℝ)*x 1 + (360187829/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1886036849/5000000000 : ℝ)^81 ≤ (29672473417251/100000000000000 : ℝ)^65 := by
    have hnat : (1886036849 : ℕ)^81*100000000000000^65 ≤ 29672473417251^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886036849 5000000000 29672473417251 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014936607/10000000000 : ℝ)^81 ≤ (5289256733901/12500000000000 : ℝ)^65 := by
    have hnat : (5014936607 : ℕ)^81*12500000000000^65 ≤ 5289256733901^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014936607 10000000000 5289256733901 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360187829/1000000000 : ℝ)^81 ≤ (875421021781/3125000000000 : ℝ)^65 := by
    have hnat : (360187829 : ℕ)^81*3125000000000^65 ≤ 875421021781^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360187829 1000000000 875421021781 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1886036849/5000000000 : ℝ), (-5014936607/10000000000 : ℝ), (360187829/1000000000 : ℝ)] ![(29672473417251/100000000000000 : ℝ), (5289256733901/12500000000000 : ℝ), (875421021781/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1886036849/5000000000 : ℝ)|^81 ≤ (29672473417251/100000000000000 : ℝ)^65
        have hw : |(-1886036849/5000000000 : ℝ)|=(1886036849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5014936607/10000000000 : ℝ)|^81 ≤ (5289256733901/12500000000000 : ℝ)^65
        have hw : |(-5014936607/10000000000 : ℝ)|=(5014936607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(360187829/1000000000 : ℝ)|^81 ≤ (875421021781/3125000000000 : ℝ)^65
        have hw : |(360187829/1000000000 : ℝ)|=(360187829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1623265887/5000000000 : ℝ)*x 0 + (1140621283/2000000000 : ℝ)*x 1 + (840803149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1623265887/5000000000 : ℝ)^81 ≤ (1538274159367/6250000000000 : ℝ)^65 := by
    have hnat : (1623265887 : ℕ)^81*6250000000000^65 ≤ 1538274159367^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623265887 5000000000 1538274159367 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140621283/2000000000 : ℝ)^81 ≤ (12417020138549/25000000000000 : ℝ)^65 := by
    have hnat : (1140621283 : ℕ)^81*25000000000000^65 ≤ 12417020138549^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140621283 2000000000 12417020138549 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840803149/2500000000 : ℝ)^81 ≤ (25719532889283/100000000000000 : ℝ)^65 := by
    have hnat : (840803149 : ℕ)^81*100000000000000^65 ≤ 25719532889283^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840803149 2500000000 25719532889283 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1623265887/5000000000 : ℝ), (1140621283/2000000000 : ℝ), (840803149/2500000000 : ℝ)] ![(1538274159367/6250000000000 : ℝ), (12417020138549/25000000000000 : ℝ), (25719532889283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1623265887/5000000000 : ℝ)|^81 ≤ (1538274159367/6250000000000 : ℝ)^65
        have hw : |(1623265887/5000000000 : ℝ)|=(1623265887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140621283/2000000000 : ℝ)|^81 ≤ (12417020138549/25000000000000 : ℝ)^65
        have hw : |(1140621283/2000000000 : ℝ)|=(1140621283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(840803149/2500000000 : ℝ)|^81 ≤ (25719532889283/100000000000000 : ℝ)^65
        have hw : |(840803149/2500000000 : ℝ)|=(840803149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (633029141/1000000000 : ℝ)*x 0 + (-1820001909/5000000000 : ℝ)*x 1 + (-43760001/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (633029141/1000000000 : ℝ)^81 ≤ (2262577035877/4000000000000 : ℝ)^65 := by
    have hnat : (633029141 : ℕ)^81*4000000000000^65 ≤ 2262577035877^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633029141 1000000000 2262577035877 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820001909/5000000000 : ℝ)^81 ≤ (28383462164509/100000000000000 : ℝ)^65 := by
    have hnat : (1820001909 : ℕ)^81*100000000000000^65 ≤ 28383462164509^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820001909 5000000000 28383462164509 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43760001/200000000 : ℝ)^81 ≤ (15052111924663/100000000000000 : ℝ)^65 := by
    have hnat : (43760001 : ℕ)^81*100000000000000^65 ≤ 15052111924663^65*200000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43760001 200000000 15052111924663 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(633029141/1000000000 : ℝ), (-1820001909/5000000000 : ℝ), (-43760001/200000000 : ℝ)] ![(2262577035877/4000000000000 : ℝ), (28383462164509/100000000000000 : ℝ), (15052111924663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(633029141/1000000000 : ℝ)|^81 ≤ (2262577035877/4000000000000 : ℝ)^65
        have hw : |(633029141/1000000000 : ℝ)|=(633029141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820001909/5000000000 : ℝ)|^81 ≤ (28383462164509/100000000000000 : ℝ)^65
        have hw : |(-1820001909/5000000000 : ℝ)|=(1820001909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43760001/200000000 : ℝ)|^81 ≤ (15052111924663/100000000000000 : ℝ)^65
        have hw : |(-43760001/200000000 : ℝ)|=(43760001/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1726909/2500000000 : ℝ)*x 0 + (-664672901/5000000000 : ℝ)*x 1 + (9344546499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1726909/2500000000 : ℝ)^81 ≤ (5758219751/50000000000000 : ℝ)^65 := by
    have hnat : (1726909 : ℕ)^81*50000000000000^65 ≤ 5758219751^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726909 2500000000 5758219751 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664672901/5000000000 : ℝ)^81 ≤ (1011179128207/12500000000000 : ℝ)^65 := by
    have hnat : (664672901 : ℕ)^81*12500000000000^65 ≤ 1011179128207^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664672901 5000000000 1011179128207 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9344546499/10000000000 : ℝ)^81 ≤ (91899050521027/100000000000000 : ℝ)^65 := by
    have hnat : (9344546499 : ℕ)^81*100000000000000^65 ≤ 91899050521027^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9344546499 10000000000 91899050521027 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1726909/2500000000 : ℝ), (-664672901/5000000000 : ℝ), (9344546499/10000000000 : ℝ)] ![(5758219751/50000000000000 : ℝ), (1011179128207/12500000000000 : ℝ), (91899050521027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1726909/2500000000 : ℝ)|^81 ≤ (5758219751/50000000000000 : ℝ)^65
        have hw : |(-1726909/2500000000 : ℝ)|=(1726909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-664672901/5000000000 : ℝ)|^81 ≤ (1011179128207/12500000000000 : ℝ)^65
        have hw : |(-664672901/5000000000 : ℝ)|=(664672901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9344546499/10000000000 : ℝ)|^81 ≤ (91899050521027/100000000000000 : ℝ)^65
        have hw : |(9344546499/10000000000 : ℝ)|=(9344546499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-408856107/1250000000 : ℝ)*x 0 + (-3013839201/10000000000 : ℝ)*x 1 + (5983002997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408856107/1250000000 : ℝ)^81 ≤ (24842327657057/100000000000000 : ℝ)^65 := by
    have hnat : (408856107 : ℕ)^81*100000000000000^65 ≤ 24842327657057^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408856107 1250000000 24842327657057 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3013839201/10000000000 : ℝ)^81 ≤ (89735331693/400000000000 : ℝ)^65 := by
    have hnat : (3013839201 : ℕ)^81*400000000000^65 ≤ 89735331693^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013839201 10000000000 89735331693 400000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5983002997/10000000000 : ℝ)^81 ≤ (26361919700633/50000000000000 : ℝ)^65 := by
    have hnat : (5983002997 : ℕ)^81*50000000000000^65 ≤ 26361919700633^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5983002997 10000000000 26361919700633 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408856107/1250000000 : ℝ), (-3013839201/10000000000 : ℝ), (5983002997/10000000000 : ℝ)] ![(24842327657057/100000000000000 : ℝ), (89735331693/400000000000 : ℝ), (26361919700633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408856107/1250000000 : ℝ)|^81 ≤ (24842327657057/100000000000000 : ℝ)^65
        have hw : |(-408856107/1250000000 : ℝ)|=(408856107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3013839201/10000000000 : ℝ)|^81 ≤ (89735331693/400000000000 : ℝ)^65
        have hw : |(-3013839201/10000000000 : ℝ)|=(3013839201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5983002997/10000000000 : ℝ)|^81 ≤ (26361919700633/50000000000000 : ℝ)^65
        have hw : |(5983002997/10000000000 : ℝ)|=(5983002997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5339541463/10000000000 : ℝ)*x 0 + (2245509159/5000000000 : ℝ)*x 1 + (2454276753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339541463/10000000000 : ℝ)^81 ≤ (45753889161921/100000000000000 : ℝ)^65 := by
    have hnat : (5339541463 : ℕ)^81*100000000000000^65 ≤ 45753889161921^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339541463 10000000000 45753889161921 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245509159/5000000000 : ℝ)^81 ≤ (18439034322093/50000000000000 : ℝ)^65 := by
    have hnat : (2245509159 : ℕ)^81*50000000000000^65 ≤ 18439034322093^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245509159 5000000000 18439034322093 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454276753/10000000000 : ℝ)^81 ≤ (8684021089129/50000000000000 : ℝ)^65 := by
    have hnat : (2454276753 : ℕ)^81*50000000000000^65 ≤ 8684021089129^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454276753 10000000000 8684021089129 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339541463/10000000000 : ℝ), (2245509159/5000000000 : ℝ), (2454276753/10000000000 : ℝ)] ![(45753889161921/100000000000000 : ℝ), (18439034322093/50000000000000 : ℝ), (8684021089129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339541463/10000000000 : ℝ)|^81 ≤ (45753889161921/100000000000000 : ℝ)^65
        have hw : |(5339541463/10000000000 : ℝ)|=(5339541463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245509159/5000000000 : ℝ)|^81 ≤ (18439034322093/50000000000000 : ℝ)^65
        have hw : |(2245509159/5000000000 : ℝ)|=(2245509159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454276753/10000000000 : ℝ)|^81 ≤ (8684021089129/50000000000000 : ℝ)^65
        have hw : |(2454276753/10000000000 : ℝ)|=(2454276753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (971751687/1250000000 : ℝ)*x 0 + (-2754556127/10000000000 : ℝ)*x 1 + (-1166968683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971751687/1250000000 : ℝ)^81 ≤ (36533998969169/50000000000000 : ℝ)^65 := by
    have hnat : (971751687 : ℕ)^81*50000000000000^65 ≤ 36533998969169^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971751687 1250000000 36533998969169 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754556127/10000000000 : ℝ)^81 ≤ (802191713407/4000000000000 : ℝ)^65 := by
    have hnat : (2754556127 : ℕ)^81*4000000000000^65 ≤ 802191713407^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754556127 10000000000 802191713407 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166968683/10000000000 : ℝ)^81 ≤ (3438604600747/50000000000000 : ℝ)^65 := by
    have hnat : (1166968683 : ℕ)^81*50000000000000^65 ≤ 3438604600747^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166968683 10000000000 3438604600747 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(971751687/1250000000 : ℝ), (-2754556127/10000000000 : ℝ), (-1166968683/10000000000 : ℝ)] ![(36533998969169/50000000000000 : ℝ), (802191713407/4000000000000 : ℝ), (3438604600747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(971751687/1250000000 : ℝ)|^81 ≤ (36533998969169/50000000000000 : ℝ)^65
        have hw : |(971751687/1250000000 : ℝ)|=(971751687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2754556127/10000000000 : ℝ)|^81 ≤ (802191713407/4000000000000 : ℝ)^65
        have hw : |(-2754556127/10000000000 : ℝ)|=(2754556127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1166968683/10000000000 : ℝ)|^81 ≤ (3438604600747/50000000000000 : ℝ)^65
        have hw : |(-1166968683/10000000000 : ℝ)|=(1166968683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-41767/2000000000 : ℝ)*x 0 + (-1724054237/10000000000 : ℝ)*x 1 + (1136507767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41767/2000000000 : ℝ)^81 ≤ (14714817/10000000000000 : ℝ)^65 := by
    have hnat : (41767 : ℕ)^81*10000000000000^65 ≤ 14714817^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41767 2000000000 14714817 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724054237/10000000000 : ℝ)^81 ≤ (279617923663/2500000000000 : ℝ)^65 := by
    have hnat : (1724054237 : ℕ)^81*2500000000000^65 ≤ 279617923663^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724054237 10000000000 279617923663 2500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136507767/1250000000 : ℝ)^81 ≤ (11101891986393/12500000000000 : ℝ)^65 := by
    have hnat : (1136507767 : ℕ)^81*12500000000000^65 ≤ 11101891986393^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136507767 1250000000 11101891986393 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41767/2000000000 : ℝ), (-1724054237/10000000000 : ℝ), (1136507767/1250000000 : ℝ)] ![(14714817/10000000000000 : ℝ), (279617923663/2500000000000 : ℝ), (11101891986393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41767/2000000000 : ℝ)|^81 ≤ (14714817/10000000000000 : ℝ)^65
        have hw : |(-41767/2000000000 : ℝ)|=(41767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724054237/10000000000 : ℝ)|^81 ≤ (279617923663/2500000000000 : ℝ)^65
        have hw : |(-1724054237/10000000000 : ℝ)|=(1724054237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136507767/1250000000 : ℝ)|^81 ≤ (11101891986393/12500000000000 : ℝ)^65
        have hw : |(1136507767/1250000000 : ℝ)|=(1136507767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3360173773/10000000000 : ℝ)*x 0 + (-1079897363/2500000000 : ℝ)*x 1 + (4714353501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3360173773/10000000000 : ℝ)^81 ≤ (3211322119951/12500000000000 : ℝ)^65 := by
    have hnat : (3360173773 : ℕ)^81*12500000000000^65 ≤ 3211322119951^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3360173773 10000000000 3211322119951 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079897363/2500000000 : ℝ)^81 ≤ (35132190932173/100000000000000 : ℝ)^65 := by
    have hnat : (1079897363 : ℕ)^81*100000000000000^65 ≤ 35132190932173^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079897363 2500000000 35132190932173 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4714353501/10000000000 : ℝ)^81 ≤ (39177232084467/100000000000000 : ℝ)^65 := by
    have hnat : (4714353501 : ℕ)^81*100000000000000^65 ≤ 39177232084467^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714353501 10000000000 39177232084467 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3360173773/10000000000 : ℝ), (-1079897363/2500000000 : ℝ), (4714353501/10000000000 : ℝ)] ![(3211322119951/12500000000000 : ℝ), (35132190932173/100000000000000 : ℝ), (39177232084467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3360173773/10000000000 : ℝ)|^81 ≤ (3211322119951/12500000000000 : ℝ)^65
        have hw : |(-3360173773/10000000000 : ℝ)|=(3360173773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079897363/2500000000 : ℝ)|^81 ≤ (35132190932173/100000000000000 : ℝ)^65
        have hw : |(-1079897363/2500000000 : ℝ)|=(1079897363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4714353501/10000000000 : ℝ)|^81 ≤ (39177232084467/100000000000000 : ℝ)^65
        have hw : |(4714353501/10000000000 : ℝ)|=(4714353501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2946725361/10000000000 : ℝ)*x 0 + (55343451/100000000 : ℝ)*x 1 + (1920198143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2946725361/10000000000 : ℝ)^81 ≤ (10906504470911/50000000000000 : ℝ)^65 := by
    have hnat : (2946725361 : ℕ)^81*50000000000000^65 ≤ 10906504470911^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946725361 10000000000 10906504470911 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55343451/100000000 : ℝ)^81 ≤ (47843286220013/100000000000000 : ℝ)^65 := by
    have hnat : (55343451 : ℕ)^81*100000000000000^65 ≤ 47843286220013^65*100000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55343451 100000000 47843286220013 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920198143/5000000000 : ℝ)^81 ≤ (6068740964183/20000000000000 : ℝ)^65 := by
    have hnat : (1920198143 : ℕ)^81*20000000000000^65 ≤ 6068740964183^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920198143 5000000000 6068740964183 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2946725361/10000000000 : ℝ), (55343451/100000000 : ℝ), (1920198143/5000000000 : ℝ)] ![(10906504470911/50000000000000 : ℝ), (47843286220013/100000000000000 : ℝ), (6068740964183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2946725361/10000000000 : ℝ)|^81 ≤ (10906504470911/50000000000000 : ℝ)^65
        have hw : |(2946725361/10000000000 : ℝ)|=(2946725361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55343451/100000000 : ℝ)|^81 ≤ (47843286220013/100000000000000 : ℝ)^65
        have hw : |(55343451/100000000 : ℝ)|=(55343451/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1920198143/5000000000 : ℝ)|^81 ≤ (6068740964183/20000000000000 : ℝ)^65
        have hw : |(1920198143/5000000000 : ℝ)|=(1920198143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s0_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7160105921/10000000000 : ℝ)*x 0 + (-2930078449/10000000000 : ℝ)*x 1 + (-467952997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7160105921/10000000000 : ℝ)^81 ≤ (2060901961161/3125000000000 : ℝ)^65 := by
    have hnat : (7160105921 : ℕ)^81*3125000000000^65 ≤ 2060901961161^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7160105921 10000000000 2060901961161 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2930078449/10000000000 : ℝ)^81 ≤ (676861085857/3125000000000 : ℝ)^65 := by
    have hnat : (2930078449 : ℕ)^81*3125000000000^65 ≤ 676861085857^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930078449 10000000000 676861085857 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467952997/2500000000 : ℝ)^81 ≤ (193618476239/1562500000000 : ℝ)^65 := by
    have hnat : (467952997 : ℕ)^81*1562500000000^65 ≤ 193618476239^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467952997 2500000000 193618476239 1562500000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7160105921/10000000000 : ℝ), (-2930078449/10000000000 : ℝ), (-467952997/2500000000 : ℝ)] ![(2060901961161/3125000000000 : ℝ), (676861085857/3125000000000 : ℝ), (193618476239/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7160105921/10000000000 : ℝ)|^81 ≤ (2060901961161/3125000000000 : ℝ)^65
        have hw : |(7160105921/10000000000 : ℝ)|=(7160105921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2930078449/10000000000 : ℝ)|^81 ≤ (676861085857/3125000000000 : ℝ)^65
        have hw : |(-2930078449/10000000000 : ℝ)|=(2930078449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467952997/2500000000 : ℝ)|^81 ≤ (193618476239/1562500000000 : ℝ)^65
        have hw : |(-467952997/2500000000 : ℝ)|=(467952997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3451382249/10000000000 : ℝ)*x 0 + (-3808561407/10000000000 : ℝ)*x 1 + (159956777/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3451382249/10000000000 : ℝ)^81 ≤ (26562458946633/100000000000000 : ℝ)^65 := by
    have hnat : (3451382249 : ℕ)^81*100000000000000^65 ≤ 26562458946633^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3451382249 10000000000 26562458946633 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3808561407/10000000000 : ℝ)^81 ≤ (30030575893653/100000000000000 : ℝ)^65 := by
    have hnat : (3808561407 : ℕ)^81*100000000000000^65 ≤ 30030575893653^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3808561407 10000000000 30030575893653 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159956777/312500000 : ℝ)^81 ≤ (21703482577939/50000000000000 : ℝ)^65 := by
    have hnat : (159956777 : ℕ)^81*50000000000000^65 ≤ 21703482577939^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159956777 312500000 21703482577939 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3451382249/10000000000 : ℝ), (-3808561407/10000000000 : ℝ), (159956777/312500000 : ℝ)] ![(26562458946633/100000000000000 : ℝ), (30030575893653/100000000000000 : ℝ), (21703482577939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3451382249/10000000000 : ℝ)|^81 ≤ (26562458946633/100000000000000 : ℝ)^65
        have hw : |(-3451382249/10000000000 : ℝ)|=(3451382249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3808561407/10000000000 : ℝ)|^81 ≤ (30030575893653/100000000000000 : ℝ)^65
        have hw : |(-3808561407/10000000000 : ℝ)|=(3808561407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159956777/312500000 : ℝ)|^81 ≤ (21703482577939/50000000000000 : ℝ)^65
        have hw : |(159956777/312500000 : ℝ)|=(159956777/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2104670749/5000000000 : ℝ)*x 0 + (1164387263/2500000000 : ℝ)*x 1 + (3537594519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104670749/5000000000 : ℝ)^81 ≤ (17009166624673/50000000000000 : ℝ)^65 := by
    have hnat : (2104670749 : ℕ)^81*50000000000000^65 ≤ 17009166624673^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104670749 5000000000 17009166624673 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164387263/2500000000 : ℝ)^81 ≤ (3858985212503/10000000000000 : ℝ)^65 := by
    have hnat : (1164387263 : ℕ)^81*10000000000000^65 ≤ 3858985212503^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164387263 2500000000 3858985212503 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3537594519/10000000000 : ℝ)^81 ≤ (13695907306263/50000000000000 : ℝ)^65 := by
    have hnat : (3537594519 : ℕ)^81*50000000000000^65 ≤ 13695907306263^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3537594519 10000000000 13695907306263 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104670749/5000000000 : ℝ), (1164387263/2500000000 : ℝ), (3537594519/10000000000 : ℝ)] ![(17009166624673/50000000000000 : ℝ), (3858985212503/10000000000000 : ℝ), (13695907306263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104670749/5000000000 : ℝ)|^81 ≤ (17009166624673/50000000000000 : ℝ)^65
        have hw : |(2104670749/5000000000 : ℝ)|=(2104670749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164387263/2500000000 : ℝ)|^81 ≤ (3858985212503/10000000000000 : ℝ)^65
        have hw : |(1164387263/2500000000 : ℝ)|=(1164387263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3537594519/10000000000 : ℝ)|^81 ≤ (13695907306263/50000000000000 : ℝ)^65
        have hw : |(3537594519/10000000000 : ℝ)|=(3537594519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5054858577/10000000000 : ℝ)*x 0 + (-835850839/2000000000 : ℝ)*x 1 + (-125344351/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5054858577/10000000000 : ℝ)^81 ≤ (21367113011743/50000000000000 : ℝ)^65 := by
    have hnat : (5054858577 : ℕ)^81*50000000000000^65 ≤ 21367113011743^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054858577 10000000000 21367113011743 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835850839/2000000000 : ℝ)^81 ≤ (33715592503513/100000000000000 : ℝ)^65 := by
    have hnat : (835850839 : ℕ)^81*100000000000000^65 ≤ 33715592503513^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835850839 2000000000 33715592503513 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125344351/400000000 : ℝ)^81 ≤ (1177509072637/5000000000000 : ℝ)^65 := by
    have hnat : (125344351 : ℕ)^81*5000000000000^65 ≤ 1177509072637^65*400000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125344351 400000000 1177509072637 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5054858577/10000000000 : ℝ), (-835850839/2000000000 : ℝ), (-125344351/400000000 : ℝ)] ![(21367113011743/50000000000000 : ℝ), (33715592503513/100000000000000 : ℝ), (1177509072637/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5054858577/10000000000 : ℝ)|^81 ≤ (21367113011743/50000000000000 : ℝ)^65
        have hw : |(5054858577/10000000000 : ℝ)|=(5054858577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-835850839/2000000000 : ℝ)|^81 ≤ (33715592503513/100000000000000 : ℝ)^65
        have hw : |(-835850839/2000000000 : ℝ)|=(835850839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125344351/400000000 : ℝ)|^81 ≤ (1177509072637/5000000000000 : ℝ)^65
        have hw : |(-125344351/400000000 : ℝ)|=(125344351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s1_5 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-239/10000000000 : ℝ)*x 0 + (-239/10000000000 : ℝ)*x 1 + (4999999997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239/10000000000 : ℝ)^81 ≤ (1987/6250000000000 : ℝ)^65 := by
    have hnat : (239 : ℕ)^81*6250000000000^65 ≤ 1987^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239 10000000000 1987 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239/10000000000 : ℝ)^81 ≤ (1987/6250000000000 : ℝ)^65 := by
    have hnat : (239 : ℕ)^81*6250000000000^65 ≤ 1987^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239 10000000000 1987 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999999997/5000000000 : ℝ)^81 ≤ (99999999925231/100000000000000 : ℝ)^65 := by
    have hnat : (4999999997 : ℕ)^81*100000000000000^65 ≤ 99999999925231^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999997 5000000000 99999999925231 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239/10000000000 : ℝ), (-239/10000000000 : ℝ), (4999999997/5000000000 : ℝ)] ![(1987/6250000000000 : ℝ), (1987/6250000000000 : ℝ), (99999999925231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239/10000000000 : ℝ)|^81 ≤ (1987/6250000000000 : ℝ)^65
        have hw : |(-239/10000000000 : ℝ)|=(239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239/10000000000 : ℝ)|^81 ≤ (1987/6250000000000 : ℝ)^65
        have hw : |(-239/10000000000 : ℝ)|=(239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999999997/5000000000 : ℝ)|^81 ≤ (99999999925231/100000000000000 : ℝ)^65
        have hw : |(4999999997/5000000000 : ℝ)|=(4999999997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320071_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1543615277/5000000000 : ℝ)*x 0 + (-399623621/1250000000 : ℝ)*x 1 + (5984305613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1543615277/5000000000 : ℝ)^81 ≤ (23116630200607/100000000000000 : ℝ)^65 := by
    have hnat : (1543615277 : ℕ)^81*100000000000000^65 ≤ 23116630200607^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543615277 5000000000 23116630200607 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399623621/1250000000 : ℝ)^81 ≤ (2414522539159/10000000000000 : ℝ)^65 := by
    have hnat : (399623621 : ℕ)^81*10000000000000^65 ≤ 2414522539159^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399623621 1250000000 2414522539159 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5984305613/10000000000 : ℝ)^81 ≤ (52738144389841/100000000000000 : ℝ)^65 := by
    have hnat : (5984305613 : ℕ)^81*100000000000000^65 ≤ 52738144389841^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984305613 10000000000 52738144389841 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1543615277/5000000000 : ℝ), (-399623621/1250000000 : ℝ), (5984305613/10000000000 : ℝ)] ![(23116630200607/100000000000000 : ℝ), (2414522539159/10000000000000 : ℝ), (52738144389841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1543615277/5000000000 : ℝ)|^81 ≤ (23116630200607/100000000000000 : ℝ)^65
        have hw : |(1543615277/5000000000 : ℝ)|=(1543615277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399623621/1250000000 : ℝ)|^81 ≤ (2414522539159/10000000000000 : ℝ)^65
        have hw : |(-399623621/1250000000 : ℝ)|=(399623621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5984305613/10000000000 : ℝ)|^81 ≤ (52738144389841/100000000000000 : ℝ)^65
        have hw : |(5984305613/10000000000 : ℝ)|=(5984305613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320071 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (1059/625 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3569067501/10000000000 : ℝ)*X 1 0+(508655931/1000000000 : ℝ)*X 1 1+(74549073/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1886036849/5000000000 : ℝ)*X 0 0+(-5014936607/10000000000 : ℝ)*X 0 1+(360187829/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1623265887/5000000000 : ℝ)*X 1 0+(1140621283/2000000000 : ℝ)*X 1 1+(840803149/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((633029141/1000000000 : ℝ)*X 2 0+(-1820001909/5000000000 : ℝ)*X 2 1+(-43760001/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1726909/2500000000 : ℝ)*X 0 0+(-664672901/5000000000 : ℝ)*X 0 1+(9344546499/10000000000 : ℝ)*X 0 2+(-1726909/2500000000 : ℝ)*X 1 0+(-664672901/5000000000 : ℝ)*X 1 1+(9344546499/10000000000 : ℝ)*X 1 2+(-1726909/2500000000 : ℝ)*X 2 0+(-664672901/5000000000 : ℝ)*X 2 1+(9344546499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-408856107/1250000000 : ℝ)*X 0 0+(-3013839201/10000000000 : ℝ)*X 0 1+(5983002997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5339541463/10000000000 : ℝ)*X 1 0+(2245509159/5000000000 : ℝ)*X 1 1+(2454276753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((971751687/1250000000 : ℝ)*X 2 0+(-2754556127/10000000000 : ℝ)*X 2 1+(-1166968683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-41767/2000000000 : ℝ)*X 0 0+(-1724054237/10000000000 : ℝ)*X 0 1+(1136507767/1250000000 : ℝ)*X 0 2+(-41767/2000000000 : ℝ)*X 1 0+(-1724054237/10000000000 : ℝ)*X 1 1+(1136507767/1250000000 : ℝ)*X 1 2+(-41767/2000000000 : ℝ)*X 2 0+(-1724054237/10000000000 : ℝ)*X 2 1+(1136507767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-3360173773/10000000000 : ℝ)*X 0 0+(-1079897363/2500000000 : ℝ)*X 0 1+(4714353501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2946725361/10000000000 : ℝ)*X 1 0+(55343451/100000000 : ℝ)*X 1 1+(1920198143/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((7160105921/10000000000 : ℝ)*X 2 0+(-2930078449/10000000000 : ℝ)*X 2 1+(-467952997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((37947/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37947/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47700428070393724096311/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81054007531/500000000000 : ℝ)*(base1) + (299571387137/500000000000 : ℝ)*(base7) + (663221/250000000000 : ℝ)*(base22) + (382759670139/1000000000000 : ℝ)*(base54) + (460862346281/500000000000 : ℝ)*(base60) + (75563083119/25000000000 : ℝ)*(major_s0_0) + (75563083119/25000000000 : ℝ)*(major_s0_1) + (2639763654621/1000000000000 : ℝ)*(major_s0_2) + (2129308666257/500000000000 : ℝ)*(sp_s0_7) + (4096524401959/1000000000000 : ℝ)*(sp_s0_8) + (742752415787/200000000000 : ℝ)*(sp_s0_9) + (416039286503/250000000000 : ℝ)*(sp_s0_13) + (241171677/1000000000000 : ℝ)*(sp_s0_20) + (15084507/1000000000000 : ℝ)*(sp_s0_21) + (1610123228617/1000000000000 : ℝ)*(f.failure) + (4096524401959/1000000000000 : ℝ)*(f.sum) + (2162858243740549/10000000000000000000000000000 : ℝ)*base63 + (657425069017083/10000000000000000000000000000 : ℝ)*base64 + (163628495429769/250000000000000000000000000 : ℝ)*base67 + (746563293141971/10000000000000000000000000000 : ℝ)*base68 + (3731748271826323/10000000000000000000000000000 : ℝ)*base70 + (156049144702937/250000000000000000000000000 : ℝ)*base73 + (13677745877937/250000000000000000000000000 : ℝ)*base74 + (56005878820231/250000000000000000000000000 : ℝ)*base76 + (47683650578853/125000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (419/2500000000000000 : ℝ)*base86 + (419/2500000000000000 : ℝ)*base88 + (419/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-6791/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-6791/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18997259046561012194067/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343945188041/500000000000 : ℝ)*(base1) + (1256951112457/1000000000000 : ℝ)*(base7) + (243298807639/1000000000000 : ℝ)*(base40) + (536619048659/1000000000000 : ℝ)*(base60) + (2321922245143/1000000000000 : ℝ)*(major_s0_0) + (2321922245143/1000000000000 : ℝ)*(major_s0_1) + (2321922245143/1000000000000 : ℝ)*(major_s0_2) + (2247963/100000000000 : ℝ)*(sp_s0_1) + (23828173/125000000000 : ℝ)*(sp_s0_13) + (3384899118813/1000000000000 : ℝ)*(sp_s0_14) + (2696986263101/1000000000000 : ℝ)*(sp_s0_15) + (674251104739/250000000000 : ℝ)*(sp_s0_16) + (225722167157/125000000000 : ℝ)*(sp_s0_20) + (172951/40000000000 : ℝ)*(sp_s0_23) + (154613403283/125000000000 : ℝ)*(f.failure) + (2697008742731/1000000000000 : ℝ)*(f.sum) + (2144395408090059/5000000000000000000000000000 : ℝ)*base63 + (3990278960935311/10000000000000000000000000000 : ℝ)*base65 + (9829826989244807/10000000000000000000000000000 : ℝ)*base66 + (2958797412755193/10000000000000000000000000000 : ℝ)*base68 + (82459516711313/1250000000000000000000000000 : ℝ)*base71 + (11132108892935311/10000000000000000000000000000 : ℝ)*base72 + (5315414059064689/10000000000000000000000000000 : ℝ)*base74 + (7896085030755193/10000000000000000000000000000 : ℝ)*base77 + (3552136844090059/5000000000000000000000000000 : ℝ)*base78 + (137/625000000000000 : ℝ)*base86 + (137/625000000000000 : ℝ)*base88 + (137/625000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2077/5000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(2077/5000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6861740927556677343507/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2848253068449/1000000000000 : ℝ)*(base1) + (1158167885117/1000000000000 : ℝ)*(base7) + (764263985611/500000000000 : ℝ)*(base40) + (521865972777/1000000000000 : ℝ)*(base60) + (396578488269/125000000000 : ℝ)*(major_s0_0) + (396578488269/125000000000 : ℝ)*(major_s0_1) + (396578488269/125000000000 : ℝ)*(major_s0_2) + (1961957/125000000000 : ℝ)*(sp_s0_7) + (61699683/500000000000 : ℝ)*(sp_s0_8) + (11077143/250000000000 : ℝ)*(sp_s0_9) + (13742581/250000000000 : ℝ)*(sp_s0_16) + (3424633730527/500000000000 : ℝ)*(sp_s0_21) + (800181337779/200000000000 : ℝ)*(sp_s0_22) + (1000232702341/250000000000 : ℝ)*(sp_s0_23) + (1690085183333/1000000000000 : ℝ)*(f.failure) + (4001030088261/1000000000000 : ℝ)*(f.sum) + (355939108048097/625000000000000000000000000 : ℝ)*base63 + (124766311341387/1250000000000000000000000000 : ℝ)*base64 + (374650435437581/1250000000000000000000000000 : ℝ)*base66 + (131677976312581/1250000000000000000000000000 : ℝ)*base69 + (167644604222371/156250000000000000000000000 : ℝ)*base70 + (57805751908613/1250000000000000000000000000 : ℝ)*base72 + (200285555158613/1250000000000000000000000000 : ℝ)*base75 + (435768213687581/1250000000000000000000000000 : ℝ)*base76 + (116050901576903/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1769/2500000000000000 : ℝ)*base87 + (1769/2500000000000000 : ℝ)*base89 + (1769/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (37947/100000 : ℝ) ^ (5 : ℝ) ≤ (196710365415487233/25000000000000000000 : ℝ) := by
    have hpowers : (37947/100000 : ℝ)^5 ≤ (196710365415487233/25000000000000000000 : ℝ)^1 := by
      have hnat : (37947 : ℕ)^5*25000000000000000000^1 ≤ 196710365415487233^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37947 100000 196710365415487233 25000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37947/100000 : ℝ)) (X := (196710365415487233/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (25196710365415487233/25000000000000000000 : ℝ) ≤ (400627501289023/400000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (25196710365415487233/25000000000000000000 : ℝ)^1 ≤ (400627501289023/400000000000000 : ℝ)^5 := by
      have hnat : (25196710365415487233 : ℕ)^1*400000000000000^5 ≤ 400627501289023^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25196710365415487233 25000000000000000000 400627501289023 400000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400627501289023/400000000000000 : ℝ)) (X := (25196710365415487233/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (12696710365415487233/12500000000000000000 : ℝ) ≤ (5015638695259717/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (12696710365415487233/12500000000000000000 : ℝ)^1 ≤ (5015638695259717/5000000000000000 : ℝ)^5 := by
      have hnat : (12696710365415487233 : ℕ)^1*5000000000000000^5 ≤ 5015638695259717^5*12500000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12696710365415487233 12500000000000000000 5015638695259717 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015638695259717/5000000000000000 : ℝ)) (X := (12696710365415487233/12500000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29881013763/7228000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(15589858293859/3794700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (37947/100000 : ℝ)) (alpha := (29881013763/7228000000000 : ℝ)) (beta := (15589858293859/3794700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37947/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29881013763/7228000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(15589858293859/3794700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6791/10000 : ℝ) ^ (5 : ℝ) ≤ (14443373841053414951/100000000000000000000 : ℝ) := by
    have hpowers : (6791/10000 : ℝ)^5 ≤ (14443373841053414951/100000000000000000000 : ℝ)^1 := by
      have hnat : (6791 : ℕ)^5*100000000000000000000^1 ≤ 14443373841053414951^1*10000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6791 10000 14443373841053414951 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6791/10000 : ℝ)) (X := (14443373841053414951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (114443373841053414951/100000000000000000000 : ℝ) ≤ (10273493027212037/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (114443373841053414951/100000000000000000000 : ℝ)^1 ≤ (10273493027212037/10000000000000000 : ℝ)^5 := by
      have hnat : (114443373841053414951 : ℕ)^1*10000000000000000^5 ≤ 10273493027212037^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114443373841053414951 100000000000000000000 10273493027212037 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10273493027212037/10000000000000000 : ℝ)) (X := (114443373841053414951/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (64443373841053414951/50000000000000000000 : ℝ) ≤ (10520627718195397/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (64443373841053414951/50000000000000000000 : ℝ)^1 ≤ (10520627718195397/10000000000000000 : ℝ)^5 := by
      have hnat : (64443373841053414951 : ℕ)^1*10000000000000000^5 ≤ 10520627718195397^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64443373841053414951 50000000000000000000 10520627718195397 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10520627718195397/10000000000000000 : ℝ)) (X := (64443373841053414951/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(273493027212037/6791000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(772295909323/21221875000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (6791/10000 : ℝ)) (alpha := (273493027212037/6791000000000000 : ℝ)) (beta := (772295909323/21221875000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (6791/10000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(273493027212037/6791000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(772295909323/21221875000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2077/5000 : ℝ) ^ (5 : ℝ) ≤ (38652935557194157/3125000000000000000 : ℝ) := by
    have hpowers : (2077/5000 : ℝ)^5 ≤ (38652935557194157/3125000000000000000 : ℝ)^1 := by
      have hnat : (2077 : ℕ)^5*3125000000000000000^1 ≤ 38652935557194157^1*5000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2077 5000 38652935557194157 3125000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2077/5000 : ℝ)) (X := (38652935557194157/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (3163652935557194157/3125000000000000000 : ℝ) ≤ (5012308193377867/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3163652935557194157/3125000000000000000 : ℝ)^1 ≤ (5012308193377867/5000000000000000 : ℝ)^5 := by
      have hnat : (3163652935557194157 : ℕ)^1*5000000000000000^5 ≤ 5012308193377867^5*3125000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163652935557194157 3125000000000000000 5012308193377867 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012308193377867/5000000000000000 : ℝ)) (X := (3163652935557194157/3125000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (1601152935557194157/1562500000000000000 : ℝ) ≤ (2009798666088209/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (1601152935557194157/1562500000000000000 : ℝ)^1 ≤ (2009798666088209/2000000000000000 : ℝ)^5 := by
      have hnat : (1601152935557194157 : ℕ)^1*2000000000000000^5 ≤ 2009798666088209^5*1562500000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1601152935557194157 1562500000000000000 2009798666088209 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009798666088209/2000000000000000 : ℝ)) (X := (1601152935557194157/1562500000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(12308193377867/2077000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(24376943685311/4154000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (2077/5000 : ℝ)) (alpha := (12308193377867/2077000000000000 : ℝ)) (beta := (24376943685311/4154000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (2077/5000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(12308193377867/2077000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(24376943685311/4154000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3451382249/10000000000 : ℝ)*X 0 0+(-3808561407/10000000000 : ℝ)*X 0 1+(159956777/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2104670749/5000000000 : ℝ)*X 1 0+(1164387263/2500000000 : ℝ)*X 1 1+(3537594519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5054858577/10000000000 : ℝ)*X 2 0+(-835850839/2000000000 : ℝ)*X 2 1+(-125344351/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_5 : ((-239/10000000000 : ℝ)*X 0 0+(-239/10000000000 : ℝ)*X 0 1+(4999999997/5000000000 : ℝ)*X 0 2+(-239/10000000000 : ℝ)*X 1 0+(-239/10000000000 : ℝ)*X 1 1+(4999999997/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s1_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1543615277/5000000000 : ℝ)*X 0 0+(-399623621/1250000000 : ℝ)*X 0 1+(5984305613/10000000000 : ℝ)*X 0 2+(1543615277/5000000000 : ℝ)*X 1 0+(-399623621/1250000000 : ℝ)*X 1 1+(5984305613/10000000000 : ℝ)*X 1 2+(1543615277/5000000000 : ℝ)*X 2 0+(-399623621/1250000000 : ℝ)*X 2 1+(5984305613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-111188150067306961848861283985255959/13724074511000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40350157297/125000000000 : ℝ)*(base1) + (220463/1000000000000 : ℝ)*(base10) + (44609/250000000000 : ℝ)*(base17) + (305473/1000000000000 : ℝ)*(base21) + (524306387041/1000000000000 : ℝ)*(base40) + (234722862659/1000000000000 : ℝ)*(base49) + (65031237079/125000000000 : ℝ)*(base60) + (4693/2500 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (1877246618061/1000000000000 : ℝ)*(major_s1_2) + (3023363225867/1000000000000 : ℝ)*(sp_s1_0) + (1350281004759/500000000000 : ℝ)*(sp_s1_1) + (2700561882481/1000000000000 : ℝ)*(sp_s1_2) + (46618061/1000000000000 : ℝ)*(sp_s1_5) + (84649842703/125000000000 : ℝ)*(sp_s1_6) + (1350281093977/500000000000 : ℝ)*(f.sum) + (1226242937255752417/14104907000000000000000000000000 : ℝ)*base62 + (1028410894609971/4154000000000000000000000000 : ℝ)*base64 + (3297418478547/33955000000000000000000000 : ℝ)*base66 + (328645167620413/2077000000000000000000000000 : ℝ)*base69 + (308698142886568969/577406000000000000000000000000 : ℝ)*base70 + (1258418653507/7297500000000000000000000 : ℝ)*base73 + (40031331361303/67910000000000000000000000 : ℝ)*base74 + (526494006047/1390000000000000000000000 : ℝ)*base76 + (19507347123545327/198229290000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p020_b037 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c320070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c320071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p020_b037 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
