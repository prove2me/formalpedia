-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:20:47.680095+00:00
-- url     : https://prove2.me/submissions/4c016afe-dc2e-4214-8b05-78643bffc337

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
theorem collision_support_c318076_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2318899311/5000000000 : ℝ)*x 0 + (-927115011/2000000000 : ℝ)*x 1 + (-3173467557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2318899311/5000000000 : ℝ)^79 ≤ (38156251247011/100000000000000 : ℝ)^63 := by
    have hnat : (2318899311 : ℕ)^79*100000000000000^63 ≤ 38156251247011^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318899311 5000000000 38156251247011 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (927115011/2000000000 : ℝ)^79 ≤ (238333204961/625000000000 : ℝ)^63 := by
    have hnat : (927115011 : ℕ)^79*625000000000^63 ≤ 238333204961^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927115011 2000000000 238333204961 625000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173467557/10000000000 : ℝ)^79 ≤ (23710435943747/100000000000000 : ℝ)^63 := by
    have hnat : (3173467557 : ℕ)^79*100000000000000^63 ≤ 23710435943747^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173467557 10000000000 23710435943747 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2318899311/5000000000 : ℝ), (-927115011/2000000000 : ℝ), (-3173467557/10000000000 : ℝ)] ![(38156251247011/100000000000000 : ℝ), (238333204961/625000000000 : ℝ), (23710435943747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2318899311/5000000000 : ℝ)|^79 ≤ (38156251247011/100000000000000 : ℝ)^63
        have hw : |(2318899311/5000000000 : ℝ)|=(2318899311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-927115011/2000000000 : ℝ)|^79 ≤ (238333204961/625000000000 : ℝ)^63
        have hw : |(-927115011/2000000000 : ℝ)|=(927115011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3173467557/10000000000 : ℝ)|^79 ≤ (23710435943747/100000000000000 : ℝ)^63
        have hw : |(-3173467557/10000000000 : ℝ)|=(3173467557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-230216277/2500000000 : ℝ)*x 0 + (-7952343533/10000000000 : ℝ)*x 1 + (2764857491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230216277/2500000000 : ℝ)^79 ≤ (2512492032143/50000000000000 : ℝ)^63 := by
    have hnat : (230216277 : ℕ)^79*50000000000000^63 ≤ 2512492032143^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230216277 2500000000 2512492032143 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7952343533/10000000000 : ℝ)^79 ≤ (75028118470591/100000000000000 : ℝ)^63 := by
    have hnat : (7952343533 : ℕ)^79*100000000000000^63 ≤ 75028118470591^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7952343533 10000000000 75028118470591 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2764857491/10000000000 : ℝ)^79 ≤ (9973448725177/50000000000000 : ℝ)^63 := by
    have hnat : (2764857491 : ℕ)^79*50000000000000^63 ≤ 9973448725177^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764857491 10000000000 9973448725177 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230216277/2500000000 : ℝ), (-7952343533/10000000000 : ℝ), (2764857491/10000000000 : ℝ)] ![(2512492032143/50000000000000 : ℝ), (75028118470591/100000000000000 : ℝ), (9973448725177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230216277/2500000000 : ℝ)|^79 ≤ (2512492032143/50000000000000 : ℝ)^63
        have hw : |(-230216277/2500000000 : ℝ)|=(230216277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7952343533/10000000000 : ℝ)|^79 ≤ (75028118470591/100000000000000 : ℝ)^63
        have hw : |(-7952343533/10000000000 : ℝ)|=(7952343533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2764857491/10000000000 : ℝ)|^79 ≤ (9973448725177/50000000000000 : ℝ)^63
        have hw : |(2764857491/10000000000 : ℝ)|=(2764857491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4695334459/10000000000 : ℝ)*x 0 + (2745617151/5000000000 : ℝ)*x 1 + (104781941/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4695334459/10000000000 : ℝ)^79 ≤ (38750762828751/100000000000000 : ℝ)^63 := by
    have hnat : (4695334459 : ℕ)^79*100000000000000^63 ≤ 38750762828751^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4695334459 10000000000 38750762828751 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745617151/5000000000 : ℝ)^79 ≤ (11789473794457/25000000000000 : ℝ)^63 := by
    have hnat : (2745617151 : ℕ)^79*25000000000000^63 ≤ 11789473794457^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745617151 5000000000 11789473794457 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104781941/500000000 : ℝ)^79 ≤ (7045670988591/50000000000000 : ℝ)^63 := by
    have hnat : (104781941 : ℕ)^79*50000000000000^63 ≤ 7045670988591^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104781941 500000000 7045670988591 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4695334459/10000000000 : ℝ), (2745617151/5000000000 : ℝ), (104781941/500000000 : ℝ)] ![(38750762828751/100000000000000 : ℝ), (11789473794457/25000000000000 : ℝ), (7045670988591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4695334459/10000000000 : ℝ)|^79 ≤ (38750762828751/100000000000000 : ℝ)^63
        have hw : |(4695334459/10000000000 : ℝ)|=(4695334459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745617151/5000000000 : ℝ)|^79 ≤ (11789473794457/25000000000000 : ℝ)^63
        have hw : |(2745617151/5000000000 : ℝ)|=(2745617151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104781941/500000000 : ℝ)|^79 ≤ (7045670988591/50000000000000 : ℝ)^63
        have hw : |(104781941/500000000 : ℝ)|=(104781941/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3110098037/5000000000 : ℝ)*x 0 + (-4587928917/10000000000 : ℝ)*x 1 + (-1229655341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3110098037/5000000000 : ℝ)^79 ≤ (27568101560689/50000000000000 : ℝ)^63 := by
    have hnat : (3110098037 : ℕ)^79*50000000000000^63 ≤ 27568101560689^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110098037 5000000000 27568101560689 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4587928917/10000000000 : ℝ)^79 ≤ (18821232693593/50000000000000 : ℝ)^63 := by
    have hnat : (4587928917 : ℕ)^79*50000000000000^63 ≤ 18821232693593^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587928917 10000000000 18821232693593 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229655341/10000000000 : ℝ)^79 ≤ (3610665732891/50000000000000 : ℝ)^63 := by
    have hnat : (1229655341 : ℕ)^79*50000000000000^63 ≤ 3610665732891^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229655341 10000000000 3610665732891 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3110098037/5000000000 : ℝ), (-4587928917/10000000000 : ℝ), (-1229655341/10000000000 : ℝ)] ![(27568101560689/50000000000000 : ℝ), (18821232693593/50000000000000 : ℝ), (3610665732891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3110098037/5000000000 : ℝ)|^79 ≤ (27568101560689/50000000000000 : ℝ)^63
        have hw : |(3110098037/5000000000 : ℝ)|=(3110098037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4587928917/10000000000 : ℝ)|^79 ≤ (18821232693593/50000000000000 : ℝ)^63
        have hw : |(-4587928917/10000000000 : ℝ)|=(4587928917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1229655341/10000000000 : ℝ)|^79 ≤ (3610665732891/50000000000000 : ℝ)^63
        have hw : |(-1229655341/10000000000 : ℝ)|=(1229655341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (71285111/312500000 : ℝ)*x 0 + (10154209/10000000000 : ℝ)*x 1 + (8727507917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71285111/312500000 : ℝ)^79 ≤ (3134505078137/20000000000000 : ℝ)^63 := by
    have hnat : (71285111 : ℕ)^79*20000000000000^63 ≤ 3134505078137^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71285111 312500000 3134505078137 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10154209/10000000000 : ℝ)^79 ≤ (2204647941/12500000000000 : ℝ)^63 := by
    have hnat : (10154209 : ℕ)^79*12500000000000^63 ≤ 2204647941^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10154209 10000000000 2204647941 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8727507917/10000000000 : ℝ)^79 ≤ (84309837418431/100000000000000 : ℝ)^63 := by
    have hnat : (8727507917 : ℕ)^79*100000000000000^63 ≤ 84309837418431^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8727507917 10000000000 84309837418431 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71285111/312500000 : ℝ), (10154209/10000000000 : ℝ), (8727507917/10000000000 : ℝ)] ![(3134505078137/20000000000000 : ℝ), (2204647941/12500000000000 : ℝ), (84309837418431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71285111/312500000 : ℝ)|^79 ≤ (3134505078137/20000000000000 : ℝ)^63
        have hw : |(71285111/312500000 : ℝ)|=(71285111/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10154209/10000000000 : ℝ)|^79 ≤ (2204647941/12500000000000 : ℝ)^63
        have hw : |(10154209/10000000000 : ℝ)|=(10154209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8727507917/10000000000 : ℝ)|^79 ≤ (84309837418431/100000000000000 : ℝ)^63
        have hw : |(8727507917/10000000000 : ℝ)|=(8727507917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-665433123/10000000000 : ℝ)*x 0 + (-1956927793/5000000000 : ℝ)*x 1 + (3581690419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (665433123/10000000000 : ℝ)^79 ≤ (3343569060733/100000000000000 : ℝ)^63 := by
    have hnat : (665433123 : ℕ)^79*100000000000000^63 ≤ 3343569060733^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665433123 10000000000 3343569060733 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956927793/5000000000 : ℝ)^79 ≤ (30841773866191/100000000000000 : ℝ)^63 := by
    have hnat : (1956927793 : ℕ)^79*100000000000000^63 ≤ 30841773866191^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956927793 5000000000 30841773866191 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3581690419/5000000000 : ℝ)^79 ≤ (13162931411629/20000000000000 : ℝ)^63 := by
    have hnat : (3581690419 : ℕ)^79*20000000000000^63 ≤ 13162931411629^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3581690419 5000000000 13162931411629 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-665433123/10000000000 : ℝ), (-1956927793/5000000000 : ℝ), (3581690419/5000000000 : ℝ)] ![(3343569060733/100000000000000 : ℝ), (30841773866191/100000000000000 : ℝ), (13162931411629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-665433123/10000000000 : ℝ)|^79 ≤ (3343569060733/100000000000000 : ℝ)^63
        have hw : |(-665433123/10000000000 : ℝ)|=(665433123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956927793/5000000000 : ℝ)|^79 ≤ (30841773866191/100000000000000 : ℝ)^63
        have hw : |(-1956927793/5000000000 : ℝ)|=(1956927793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3581690419/5000000000 : ℝ)|^79 ≤ (13162931411629/20000000000000 : ℝ)^63
        have hw : |(3581690419/5000000000 : ℝ)|=(3581690419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7964485659/10000000000 : ℝ)*x 0 + (4002019/16000000 : ℝ)*x 1 + (615849557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7964485659/10000000000 : ℝ)^79 ≤ (75171797823623/100000000000000 : ℝ)^63 := by
    have hnat : (7964485659 : ℕ)^79*100000000000000^63 ≤ 75171797823623^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7964485659 10000000000 75171797823623 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002019/16000000 : ℝ)^79 ≤ (17591816939087/100000000000000 : ℝ)^63 := by
    have hnat : (4002019 : ℕ)^79*100000000000000^63 ≤ 17591816939087^63*16000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002019 16000000 17591816939087 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615849557/5000000000 : ℝ)^79 ≤ (1809096303881/25000000000000 : ℝ)^63 := by
    have hnat : (615849557 : ℕ)^79*25000000000000^63 ≤ 1809096303881^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615849557 5000000000 1809096303881 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7964485659/10000000000 : ℝ), (4002019/16000000 : ℝ), (615849557/5000000000 : ℝ)] ![(75171797823623/100000000000000 : ℝ), (17591816939087/100000000000000 : ℝ), (1809096303881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7964485659/10000000000 : ℝ)|^79 ≤ (75171797823623/100000000000000 : ℝ)^63
        have hw : |(7964485659/10000000000 : ℝ)|=(7964485659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4002019/16000000 : ℝ)|^79 ≤ (17591816939087/100000000000000 : ℝ)^63
        have hw : |(4002019/16000000 : ℝ)|=(4002019/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615849557/5000000000 : ℝ)|^79 ≤ (1809096303881/25000000000000 : ℝ)^63
        have hw : |(615849557/5000000000 : ℝ)|=(615849557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (936217789/2000000000 : ℝ)*x 0 + (-3057491527/5000000000 : ℝ)*x 1 + (-314387907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936217789/2000000000 : ℝ)^79 ≤ (9650848052177/25000000000000 : ℝ)^63 := by
    have hnat : (936217789 : ℕ)^79*25000000000000^63 ≤ 9650848052177^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936217789 2000000000 9650848052177 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3057491527/5000000000 : ℝ)^79 ≤ (53969256417117/100000000000000 : ℝ)^63 := by
    have hnat : (3057491527 : ℕ)^79*100000000000000^63 ≤ 53969256417117^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3057491527 5000000000 53969256417117 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314387907/2500000000 : ℝ)^79 ≤ (3713675682309/50000000000000 : ℝ)^63 := by
    have hnat : (314387907 : ℕ)^79*50000000000000^63 ≤ 3713675682309^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314387907 2500000000 3713675682309 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(936217789/2000000000 : ℝ), (-3057491527/5000000000 : ℝ), (-314387907/2500000000 : ℝ)] ![(9650848052177/25000000000000 : ℝ), (53969256417117/100000000000000 : ℝ), (3713675682309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(936217789/2000000000 : ℝ)|^79 ≤ (9650848052177/25000000000000 : ℝ)^63
        have hw : |(936217789/2000000000 : ℝ)|=(936217789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3057491527/5000000000 : ℝ)|^79 ≤ (53969256417117/100000000000000 : ℝ)^63
        have hw : |(-3057491527/5000000000 : ℝ)|=(3057491527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-314387907/2500000000 : ℝ)|^79 ≤ (3713675682309/50000000000000 : ℝ)^63
        have hw : |(-314387907/2500000000 : ℝ)|=(314387907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (319339853/2500000000 : ℝ)*x 0 + (-21344331/10000000000 : ℝ)*x 1 + (9387562169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319339853/2500000000 : ℝ)^79 ≤ (7574343800531/100000000000000 : ℝ)^63 := by
    have hnat : (319339853 : ℕ)^79*100000000000000^63 ≤ 7574343800531^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319339853 2500000000 7574343800531 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21344331/10000000000 : ℝ)^79 ≤ (22385928029/50000000000000 : ℝ)^63 := by
    have hnat : (21344331 : ℕ)^79*50000000000000^63 ≤ 22385928029^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21344331 10000000000 22385928029 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9387562169/10000000000 : ℝ)^79 ≤ (5773805270983/6250000000000 : ℝ)^63 := by
    have hnat : (9387562169 : ℕ)^79*6250000000000^63 ≤ 5773805270983^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9387562169 10000000000 5773805270983 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(319339853/2500000000 : ℝ), (-21344331/10000000000 : ℝ), (9387562169/10000000000 : ℝ)] ![(7574343800531/100000000000000 : ℝ), (22385928029/50000000000000 : ℝ), (5773805270983/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(319339853/2500000000 : ℝ)|^79 ≤ (7574343800531/100000000000000 : ℝ)^63
        have hw : |(319339853/2500000000 : ℝ)|=(319339853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21344331/10000000000 : ℝ)|^79 ≤ (22385928029/50000000000000 : ℝ)^63
        have hw : |(-21344331/10000000000 : ℝ)|=(21344331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9387562169/10000000000 : ℝ)|^79 ≤ (5773805270983/6250000000000 : ℝ)^63
        have hw : |(9387562169/10000000000 : ℝ)|=(9387562169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-17258889/625000000 : ℝ)*x 0 + (-8327769697/10000000000 : ℝ)*x 1 + (1351794687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17258889/625000000 : ℝ)^79 ≤ (34680077843/3125000000000 : ℝ)^63 := by
    have hnat : (17258889 : ℕ)^79*3125000000000^63 ≤ 34680077843^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17258889 625000000 34680077843 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8327769697/10000000000 : ℝ)^79 ≤ (15899208926281/20000000000000 : ℝ)^63 := by
    have hnat : (8327769697 : ℕ)^79*20000000000000^63 ≤ 15899208926281^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8327769697 10000000000 15899208926281 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351794687/5000000000 : ℝ)^79 ≤ (9697096432359/50000000000000 : ℝ)^63 := by
    have hnat : (1351794687 : ℕ)^79*50000000000000^63 ≤ 9697096432359^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351794687 5000000000 9697096432359 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17258889/625000000 : ℝ), (-8327769697/10000000000 : ℝ), (1351794687/5000000000 : ℝ)] ![(34680077843/3125000000000 : ℝ), (15899208926281/20000000000000 : ℝ), (9697096432359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17258889/625000000 : ℝ)|^79 ≤ (34680077843/3125000000000 : ℝ)^63
        have hw : |(-17258889/625000000 : ℝ)|=(17258889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8327769697/10000000000 : ℝ)|^79 ≤ (15899208926281/20000000000000 : ℝ)^63
        have hw : |(-8327769697/10000000000 : ℝ)|=(8327769697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351794687/5000000000 : ℝ)|^79 ≤ (9697096432359/50000000000000 : ℝ)^63
        have hw : |(1351794687/5000000000 : ℝ)|=(1351794687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (200548001/250000000 : ℝ)*x 0 + (2186443797/10000000000 : ℝ)*x 1 + (1502797783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200548001/250000000 : ℝ)^79 ≤ (75852179313391/100000000000000 : ℝ)^63 := by
    have hnat : (200548001 : ℕ)^79*100000000000000^63 ≤ 75852179313391^63*250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200548001 250000000 75852179313391 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186443797/10000000000 : ℝ)^79 ≤ (14861163481571/100000000000000 : ℝ)^63 := by
    have hnat : (2186443797 : ℕ)^79*100000000000000^63 ≤ 14861163481571^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186443797 10000000000 14861163481571 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1502797783/10000000000 : ℝ)^79 ≤ (2321664298893/25000000000000 : ℝ)^63 := by
    have hnat : (1502797783 : ℕ)^79*25000000000000^63 ≤ 2321664298893^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502797783 10000000000 2321664298893 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(200548001/250000000 : ℝ), (2186443797/10000000000 : ℝ), (1502797783/10000000000 : ℝ)] ![(75852179313391/100000000000000 : ℝ), (14861163481571/100000000000000 : ℝ), (2321664298893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(200548001/250000000 : ℝ)|^79 ≤ (75852179313391/100000000000000 : ℝ)^63
        have hw : |(200548001/250000000 : ℝ)|=(200548001/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2186443797/10000000000 : ℝ)|^79 ≤ (14861163481571/100000000000000 : ℝ)^63
        have hw : |(2186443797/10000000000 : ℝ)|=(2186443797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1502797783/10000000000 : ℝ)|^79 ≤ (2321664298893/25000000000000 : ℝ)^63
        have hw : |(1502797783/10000000000 : ℝ)|=(1502797783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (475749051/2000000000 : ℝ)*x 0 + (-1495831417/2000000000 : ℝ)*x 1 + (-1042935517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475749051/2000000000 : ℝ)^79 ≤ (8259050341623/50000000000000 : ℝ)^63 := by
    have hnat : (475749051 : ℕ)^79*50000000000000^63 ≤ 8259050341623^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475749051 2000000000 8259050341623 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1495831417/2000000000 : ℝ)^79 ≤ (17368217236069/25000000000000 : ℝ)^63 := by
    have hnat : (1495831417 : ℕ)^79*25000000000000^63 ≤ 17368217236069^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1495831417 2000000000 17368217236069 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042935517/5000000000 : ℝ)^79 ≤ (7004515176093/50000000000000 : ℝ)^63 := by
    have hnat : (1042935517 : ℕ)^79*50000000000000^63 ≤ 7004515176093^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042935517 5000000000 7004515176093 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(475749051/2000000000 : ℝ), (-1495831417/2000000000 : ℝ), (-1042935517/5000000000 : ℝ)] ![(8259050341623/50000000000000 : ℝ), (17368217236069/25000000000000 : ℝ), (7004515176093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(475749051/2000000000 : ℝ)|^79 ≤ (8259050341623/50000000000000 : ℝ)^63
        have hw : |(475749051/2000000000 : ℝ)|=(475749051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1495831417/2000000000 : ℝ)|^79 ≤ (17368217236069/25000000000000 : ℝ)^63
        have hw : |(-1495831417/2000000000 : ℝ)|=(1495831417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1042935517/5000000000 : ℝ)|^79 ≤ (7004515176093/50000000000000 : ℝ)^63
        have hw : |(-1042935517/5000000000 : ℝ)|=(1042935517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s0_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6805535217/10000000000 : ℝ)*x 0 + (-11319/10000000000 : ℝ)*x 1 + (2324972491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6805535217/10000000000 : ℝ)^79 ≤ (7714799172581/12500000000000 : ℝ)^63 := by
    have hnat : (6805535217 : ℕ)^79*12500000000000^63 ≤ 7714799172581^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6805535217 10000000000 7714799172581 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11319/10000000000 : ℝ)^79 ≤ (1748373/50000000000000 : ℝ)^63 := by
    have hnat : (11319 : ℕ)^79*50000000000000^63 ≤ 1748373^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11319 10000000000 1748373 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2324972491/5000000000 : ℝ)^79 ≤ (598150048711/1562500000000 : ℝ)^63 := by
    have hnat : (2324972491 : ℕ)^79*1562500000000^63 ≤ 598150048711^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2324972491 5000000000 598150048711 1562500000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6805535217/10000000000 : ℝ), (-11319/10000000000 : ℝ), (2324972491/5000000000 : ℝ)] ![(7714799172581/12500000000000 : ℝ), (1748373/50000000000000 : ℝ), (598150048711/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6805535217/10000000000 : ℝ)|^79 ≤ (7714799172581/12500000000000 : ℝ)^63
        have hw : |(6805535217/10000000000 : ℝ)|=(6805535217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11319/10000000000 : ℝ)|^79 ≤ (1748373/50000000000000 : ℝ)^63
        have hw : |(-11319/10000000000 : ℝ)|=(11319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2324972491/5000000000 : ℝ)|^79 ≤ (598150048711/1562500000000 : ℝ)^63
        have hw : |(2324972491/5000000000 : ℝ)|=(2324972491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005391747/5000000000 : ℝ)*x 0 + (-5402580741/10000000000 : ℝ)*x 1 + (606935407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005391747/5000000000 : ℝ)^79 ≤ (13379571849153/100000000000000 : ℝ)^63 := by
    have hnat : (1005391747 : ℕ)^79*100000000000000^63 ≤ 13379571849153^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005391747 5000000000 13379571849153 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402580741/10000000000 : ℝ)^79 ≤ (46205159793531/100000000000000 : ℝ)^63 := by
    have hnat : (5402580741 : ℕ)^79*100000000000000^63 ≤ 46205159793531^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402580741 10000000000 46205159793531 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606935407/1250000000 : ℝ)^79 ≤ (40415268345133/100000000000000 : ℝ)^63 := by
    have hnat : (606935407 : ℕ)^79*100000000000000^63 ≤ 40415268345133^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606935407 1250000000 40415268345133 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005391747/5000000000 : ℝ), (-5402580741/10000000000 : ℝ), (606935407/1250000000 : ℝ)] ![(13379571849153/100000000000000 : ℝ), (46205159793531/100000000000000 : ℝ), (40415268345133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005391747/5000000000 : ℝ)|^79 ≤ (13379571849153/100000000000000 : ℝ)^63
        have hw : |(-1005391747/5000000000 : ℝ)|=(1005391747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5402580741/10000000000 : ℝ)|^79 ≤ (46205159793531/100000000000000 : ℝ)^63
        have hw : |(-5402580741/10000000000 : ℝ)|=(5402580741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606935407/1250000000 : ℝ)|^79 ≤ (40415268345133/100000000000000 : ℝ)^63
        have hw : |(606935407/1250000000 : ℝ)|=(606935407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5608789047/10000000000 : ℝ)*x 0 + (917153617/2500000000 : ℝ)*x 1 + (3111866059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5608789047/10000000000 : ℝ)^79 ≤ (24213626311733/50000000000000 : ℝ)^63 := by
    have hnat : (5608789047 : ℕ)^79*50000000000000^63 ≤ 24213626311733^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608789047 10000000000 24213626311733 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917153617/2500000000 : ℝ)^79 ≤ (7109506168797/25000000000000 : ℝ)^63 := by
    have hnat : (917153617 : ℕ)^79*25000000000000^63 ≤ 7109506168797^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917153617 2500000000 7109506168797 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3111866059/10000000000 : ℝ)^79 ≤ (23134722680841/100000000000000 : ℝ)^63 := by
    have hnat : (3111866059 : ℕ)^79*100000000000000^63 ≤ 23134722680841^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111866059 10000000000 23134722680841 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5608789047/10000000000 : ℝ), (917153617/2500000000 : ℝ), (3111866059/10000000000 : ℝ)] ![(24213626311733/50000000000000 : ℝ), (7109506168797/25000000000000 : ℝ), (23134722680841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5608789047/10000000000 : ℝ)|^79 ≤ (24213626311733/50000000000000 : ℝ)^63
        have hw : |(5608789047/10000000000 : ℝ)|=(5608789047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917153617/2500000000 : ℝ)|^79 ≤ (7109506168797/25000000000000 : ℝ)^63
        have hw : |(917153617/2500000000 : ℝ)|=(917153617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3111866059/10000000000 : ℝ)|^79 ≤ (23134722680841/100000000000000 : ℝ)^63
        have hw : |(3111866059/10000000000 : ℝ)|=(3111866059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (90167573/200000000 : ℝ)*x 0 + (-4408126459/10000000000 : ℝ)*x 1 + (-355855267/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90167573/200000000 : ℝ)^79 ≤ (1841291506819/5000000000000 : ℝ)^63 := by
    have hnat : (90167573 : ℕ)^79*5000000000000^63 ≤ 1841291506819^63*200000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90167573 200000000 1841291506819 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408126459/10000000000 : ℝ)^79 ≤ (8950470686191/25000000000000 : ℝ)^63 := by
    have hnat : (4408126459 : ℕ)^79*25000000000000^63 ≤ 8950470686191^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408126459 10000000000 8950470686191 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355855267/1000000000 : ℝ)^79 ≤ (6843071776217/25000000000000 : ℝ)^63 := by
    have hnat : (355855267 : ℕ)^79*25000000000000^63 ≤ 6843071776217^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355855267 1000000000 6843071776217 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90167573/200000000 : ℝ), (-4408126459/10000000000 : ℝ), (-355855267/1000000000 : ℝ)] ![(1841291506819/5000000000000 : ℝ), (8950470686191/25000000000000 : ℝ), (6843071776217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90167573/200000000 : ℝ)|^79 ≤ (1841291506819/5000000000000 : ℝ)^63
        have hw : |(90167573/200000000 : ℝ)|=(90167573/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4408126459/10000000000 : ℝ)|^79 ≤ (8950470686191/25000000000000 : ℝ)^63
        have hw : |(-4408126459/10000000000 : ℝ)|=(4408126459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355855267/1000000000 : ℝ)|^79 ≤ (6843071776217/25000000000000 : ℝ)^63
        have hw : |(-355855267/1000000000 : ℝ)|=(355855267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318076_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (931192133/2000000000 : ℝ)*x 0 + (-277063927/2500000000 : ℝ)*x 1 + (623649743/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931192133/2000000000 : ℝ)^79 ≤ (19171858244559/50000000000000 : ℝ)^63 := by
    have hnat : (931192133 : ℕ)^79*50000000000000^63 ≤ 19171858244559^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931192133 2000000000 19171858244559 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277063927/2500000000 : ℝ)^79 ≤ (1584706606441/25000000000000 : ℝ)^63 := by
    have hnat : (277063927 : ℕ)^79*25000000000000^63 ≤ 1584706606441^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277063927 2500000000 1584706606441 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623649743/1000000000 : ℝ)^79 ≤ (55317457065239/100000000000000 : ℝ)^63 := by
    have hnat : (623649743 : ℕ)^79*100000000000000^63 ≤ 55317457065239^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623649743 1000000000 55317457065239 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(931192133/2000000000 : ℝ), (-277063927/2500000000 : ℝ), (623649743/1000000000 : ℝ)] ![(19171858244559/50000000000000 : ℝ), (1584706606441/25000000000000 : ℝ), (55317457065239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(931192133/2000000000 : ℝ)|^79 ≤ (19171858244559/50000000000000 : ℝ)^63
        have hw : |(931192133/2000000000 : ℝ)|=(931192133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277063927/2500000000 : ℝ)|^79 ≤ (1584706606441/25000000000000 : ℝ)^63
        have hw : |(-277063927/2500000000 : ℝ)|=(277063927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(623649743/1000000000 : ℝ)|^79 ≤ (55317457065239/100000000000000 : ℝ)^63
        have hw : |(623649743/1000000000 : ℝ)|=(623649743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318076 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_2 : ((2318899311/5000000000 : ℝ)*X 2 0+(-927115011/2000000000 : ℝ)*X 2 1+(-3173467557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-230216277/2500000000 : ℝ)*X 0 0+(-7952343533/10000000000 : ℝ)*X 0 1+(2764857491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4695334459/10000000000 : ℝ)*X 1 0+(2745617151/5000000000 : ℝ)*X 1 1+(104781941/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3110098037/5000000000 : ℝ)*X 2 0+(-4587928917/10000000000 : ℝ)*X 2 1+(-1229655341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((71285111/312500000 : ℝ)*X 0 0+(10154209/10000000000 : ℝ)*X 0 1+(8727507917/10000000000 : ℝ)*X 0 2+(71285111/312500000 : ℝ)*X 1 0+(10154209/10000000000 : ℝ)*X 1 1+(8727507917/10000000000 : ℝ)*X 1 2+(71285111/312500000 : ℝ)*X 2 0+(10154209/10000000000 : ℝ)*X 2 1+(8727507917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-665433123/10000000000 : ℝ)*X 0 0+(-1956927793/5000000000 : ℝ)*X 0 1+(3581690419/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((7964485659/10000000000 : ℝ)*X 1 0+(4002019/16000000 : ℝ)*X 1 1+(615849557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((936217789/2000000000 : ℝ)*X 2 0+(-3057491527/5000000000 : ℝ)*X 2 1+(-314387907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((319339853/2500000000 : ℝ)*X 0 0+(-21344331/10000000000 : ℝ)*X 0 1+(9387562169/10000000000 : ℝ)*X 0 2+(319339853/2500000000 : ℝ)*X 1 0+(-21344331/10000000000 : ℝ)*X 1 1+(9387562169/10000000000 : ℝ)*X 1 2+(319339853/2500000000 : ℝ)*X 2 0+(-21344331/10000000000 : ℝ)*X 2 1+(9387562169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-17258889/625000000 : ℝ)*X 0 0+(-8327769697/10000000000 : ℝ)*X 0 1+(1351794687/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((200548001/250000000 : ℝ)*X 1 0+(2186443797/10000000000 : ℝ)*X 1 1+(1502797783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((475749051/2000000000 : ℝ)*X 2 0+(-1495831417/2000000000 : ℝ)*X 2 1+(-1042935517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((6805535217/10000000000 : ℝ)*X 0 0+(-11319/10000000000 : ℝ)*X 0 1+(2324972491/5000000000 : ℝ)*X 0 2+(6805535217/10000000000 : ℝ)*X 1 0+(-11319/10000000000 : ℝ)*X 1 1+(2324972491/5000000000 : ℝ)*X 1 2+(6805535217/10000000000 : ℝ)*X 2 0+(-11319/10000000000 : ℝ)*X 2 1+(2324972491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((35399/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35399/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21357345828600289573023/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123576295779/500000000000 : ℝ)*(base3) + (434528521389/500000000000 : ℝ)*(base7) + (315293/250000000000 : ℝ)*(base40) + (115668663461/125000000000 : ℝ)*(base54) + (1916411453473/1000000000000 : ℝ)*(major_s0_0) + (1916411453473/1000000000000 : ℝ)*(major_s0_1) + (198212429157/200000000000 : ℝ)*(major_s0_2) + (5839233/100000000000 : ℝ)*(sp_s0_2) + (2286222946567/1000000000000 : ℝ)*(sp_s0_7) + (4053400861/1600000000 : ℝ)*(sp_s0_8) + (340199152863/250000000000 : ℝ)*(sp_s0_9) + (93346738313/125000000000 : ℝ)*(sp_s0_13) + (9317549/500000000000 : ℝ)*(sp_s0_16) + (424129/31250000000 : ℝ)*(sp_s0_20) + (10502323351/10000000000 : ℝ)*(f.failure) + (2286222946567/1000000000000 : ℝ)*(f.sum) + (79568406600659/2500000000000000000000000000 : ℝ)*base62 + (163852451682927/1000000000000000000000000000 : ℝ)*base65 + (3155288686507707/5000000000000000000000000000 : ℝ)*base66 + (75839952935463/1000000000000000000000000000 : ℝ)*base68 + (86303644380817/312500000000000000000000000 : ℝ)*base70 + (1572061295975997/5000000000000000000000000000 : ℝ)*base72 + (1940679485024003/5000000000000000000000000000 : ℝ)*base74 + (1137484890992293/5000000000000000000000000000 : ℝ)*base77 + (181591013627037/625000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (29/40000000000000 : ℝ)*base87 + (29/40000000000000 : ℝ)*base89 + (29/40000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-66609/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-66609/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24970221597662657182017/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3471221/1000000000000 : ℝ)*(base3) + (730987422999/1000000000000 : ℝ)*(base7) + (12460424533/20000000000 : ℝ)*(base33) + (4462427/1000000000000 : ℝ)*(base54) + (4478031/1000000000000 : ℝ)*(base60) + (451179581757/500000000000 : ℝ)*(major_s0_0) + (381345097541/250000000000 : ℝ)*(major_s0_1) + (1525375927737/1000000000000 : ℝ)*(major_s0_2) + (21107603/500000000000 : ℝ)*(sp_s0_13) + (449328650187/250000000000 : ℝ)*(sp_s0_14) + (234830008283/200000000000 : ℝ)*(sp_s0_15) + (146786113959/125000000000 : ℝ)*(sp_s0_16) + (97929791107/62500000000 : ℝ)*(sp_s0_20) + (29360781/200000000000 : ℝ)*(sp_s0_22) + (835939383567/1000000000000 : ℝ)*(f.failure) + (449328650187/250000000000 : ℝ)*(f.sum) + (1026217642465887/5000000000000000000000000000 : ℝ)*base62 + (1392116840064693/5000000000000000000000000000 : ℝ)*base64 + (480254800597481/1250000000000000000000000000 : ℝ)*base67 + (532168967839683/5000000000000000000000000000 : ℝ)*base68 + (442351426137581/5000000000000000000000000000 : ℝ)*base71 + (71529901271527/2500000000000000000000000000 : ℝ)*base73 + (276677483218449/1250000000000000000000000000 : ℝ)*base75 + (50392455898863/2500000000000000000000000000 : ℝ)*base76 + (812064751216489/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (467/4000000000000000 : ℝ)*base86 + (467/4000000000000000 : ℝ)*base88 + (467/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18799/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18799/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (111408721545622594497/6250000000000000000000000 : ℝ) := by norm_num
    linear_combination (452042069429/1000000000000 : ℝ)*(base3) + (14501035277/12500000000 : ℝ)*(base7) + (13888201173/200000000000 : ℝ)*(base40) + (830617/1000000000000 : ℝ)*(base49) + (44620444013/25000000000 : ℝ)*(major_s0_0) + (44620444013/25000000000 : ℝ)*(major_s0_1) + (44620444013/25000000000 : ℝ)*(major_s0_2) + (2877563/125000000000 : ℝ)*(sp_s0_7) + (48812281/500000000000 : ℝ)*(sp_s0_15) + (27844371/1000000000000 : ℝ)*(sp_s0_16) + (385781786357/200000000000 : ℝ)*(sp_s0_21) + (595219099289/250000000000 : ℝ)*(sp_s0_22) + (1928904107917/1000000000000 : ℝ)*(sp_s0_23) + (8430785379/5000000000 : ℝ)*(sp_s0_27) + (978116323069/1000000000000 : ℝ)*(f.failure) + (1928931952289/1000000000000 : ℝ)*(f.sum) + (990011169751/12500000000000000000000000 : ℝ)*base62 + (98432117916443/125000000000000000000000000 : ℝ)*base65 + (101521735068567/125000000000000000000000000 : ℝ)*base66 + (136740829368567/125000000000000000000000000 : ℝ)*base68 + (777960712043/3906250000000000000000000 : ℝ)*base71 + (144103866996057/125000000000000000000000000 : ℝ)*base72 + (44229756078943/125000000000000000000000000 : ℝ)*base74 + (52751950343933/125000000000000000000000000 : ℝ)*base77 + (378523394979/488281250000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (631/4000000000000000 : ℝ)*base87 + (631/4000000000000000 : ℝ)*base89 + (631/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (35399/50000 : ℝ) ^ (39/8 : ℝ) ≤ (4642932090770779589/25000000000000000000 : ℝ) := by
    have hpowers : (35399/50000 : ℝ)^39 ≤ (4642932090770779589/25000000000000000000 : ℝ)^8 := by
      have hnat : (35399 : ℕ)^39*25000000000000000000^8 ≤ 4642932090770779589^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35399 50000 4642932090770779589 25000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35399/50000 : ℝ)) (X := (4642932090770779589/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (29642932090770779589/25000000000000000000 : ℝ) ≤ (10355608435344389/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (29642932090770779589/25000000000000000000 : ℝ)^8 ≤ (10355608435344389/10000000000000000 : ℝ)^39 := by
      have hnat : (29642932090770779589 : ℕ)^8*10000000000000000^39 ≤ 10355608435344389^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29642932090770779589 25000000000000000000 10355608435344389 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10355608435344389/10000000000000000 : ℝ)) (X := (29642932090770779589/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (17142932090770779589/12500000000000000000 : ℝ) ≤ (426774509315943/400000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (17142932090770779589/12500000000000000000 : ℝ)^8 ≤ (426774509315943/400000000000000 : ℝ)^39 := by
      have hnat : (17142932090770779589 : ℕ)^8*400000000000000^39 ≤ 426774509315943^39*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17142932090770779589 12500000000000000000 426774509315943 400000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (426774509315943/400000000000000 : ℝ)) (X := (17142932090770779589/12500000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(355608435344389/7079800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(156877148777093/3539900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (35399/50000 : ℝ)) (alpha := (355608435344389/7079800000000000 : ℝ)) (beta := (156877148777093/3539900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35399/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(355608435344389/7079800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(156877148777093/3539900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (66609/100000 : ℝ) ^ (39/8 : ℝ) ≤ (107773747504347487/781250000000000000 : ℝ) := by
    have hpowers : (66609/100000 : ℝ)^39 ≤ (107773747504347487/781250000000000000 : ℝ)^8 := by
      have hnat : (66609 : ℕ)^39*781250000000000000^8 ≤ 107773747504347487^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66609 100000 107773747504347487 781250000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66609/100000 : ℝ)) (X := (107773747504347487/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (889023747504347487/781250000000000000 : ℝ) ≤ (5134314676860571/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (889023747504347487/781250000000000000 : ℝ)^8 ≤ (5134314676860571/5000000000000000 : ℝ)^39 := by
      have hnat : (889023747504347487 : ℕ)^8*5000000000000000^39 ≤ 5134314676860571^39*781250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        889023747504347487 781250000000000000 5134314676860571 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5134314676860571/5000000000000000 : ℝ)) (X := (889023747504347487/781250000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (498398747504347487/390625000000000000 : ℝ) ≤ (2628125142301211/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (498398747504347487/390625000000000000 : ℝ)^8 ≤ (2628125142301211/2500000000000000 : ℝ)^39 := by
      have hnat : (498398747504347487 : ℕ)^8*2500000000000000^39 ≤ 2628125142301211^39*390625000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        498398747504347487 390625000000000000 2628125142301211 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2628125142301211/2500000000000000 : ℝ)) (X := (498398747504347487/390625000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(134314676860571/3330450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(40645202580617/1110150000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (66609/100000 : ℝ)) (alpha := (134314676860571/3330450000000000 : ℝ)) (beta := (40645202580617/1110150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (66609/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(134314676860571/3330450000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(40645202580617/1110150000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (18799/25000 : ℝ) ^ (39/8 : ℝ) ≤ (12457169046802076387/50000000000000000000 : ℝ) := by
    have hpowers : (18799/25000 : ℝ)^39 ≤ (12457169046802076387/50000000000000000000 : ℝ)^8 := by
      have hnat : (18799 : ℕ)^39*50000000000000000000^8 ≤ 12457169046802076387^8*25000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18799 25000 12457169046802076387 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18799/25000 : ℝ)) (X := (12457169046802076387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (62457169046802076387/50000000000000000000 : ℝ) ≤ (1046689592414609/1000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (62457169046802076387/50000000000000000000 : ℝ)^8 ≤ (1046689592414609/1000000000000000 : ℝ)^39 := by
      have hnat : (62457169046802076387 : ℕ)^8*1000000000000000^39 ≤ 1046689592414609^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62457169046802076387 50000000000000000000 1046689592414609 1000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1046689592414609/1000000000000000 : ℝ)) (X := (62457169046802076387/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (37457169046802076387/25000000000000000000 : ℝ) ≤ (10864743439957781/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (37457169046802076387/25000000000000000000 : ℝ)^8 ≤ (10864743439957781/10000000000000000 : ℝ)^39 := by
      have hnat : (37457169046802076387 : ℕ)^8*10000000000000000^39 ≤ 10864743439957781^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37457169046802076387 25000000000000000000 10864743439957781 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10864743439957781/10000000000000000 : ℝ)) (X := (37457169046802076387/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(46689592414609/751960000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(36167955982881/683600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (18799/25000 : ℝ)) (alpha := (46689592414609/751960000000000 : ℝ)) (beta := (36167955982881/683600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (18799/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(46689592414609/751960000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(36167955982881/683600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1005391747/5000000000 : ℝ)*X 0 0+(-5402580741/10000000000 : ℝ)*X 0 1+(606935407/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5608789047/10000000000 : ℝ)*X 1 0+(917153617/2500000000 : ℝ)*X 1 1+(3111866059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((90167573/200000000 : ℝ)*X 2 0+(-4408126459/10000000000 : ℝ)*X 2 1+(-355855267/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((931192133/2000000000 : ℝ)*X 0 0+(-277063927/2500000000 : ℝ)*X 0 1+(623649743/1000000000 : ℝ)*X 0 2+(931192133/2000000000 : ℝ)*X 1 0+(-277063927/2500000000 : ℝ)*X 1 1+(623649743/1000000000 : ℝ)*X 1 2+(931192133/2000000000 : ℝ)*X 2 0+(-277063927/2500000000 : ℝ)*X 2 1+(623649743/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318076_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-2909184076914647619036493008189773959/369383429490075000000000000000000000 : ℝ) := by norm_num
    linear_combination (28409/250000000000 : ℝ)*(base1) + (8341/1000000000000 : ℝ)*(base10) + (22567/1000000000000 : ℝ)*(base17) + (4417/500000000000 : ℝ)*(base21) + (465021315243/1000000000000 : ℝ)*(base40) + (197737/1000000000000 : ℝ)*(base43) + (10877848499/100000000000 : ℝ)*(base49) + (12441354243/62500000000 : ℝ)*(base59) + (7299/4000 : ℝ)*(major_s1_0) + (1824749802263/1000000000000 : ℝ)*(major_s1_1) + (7299/4000 : ℝ)*(major_s1_2) + (1312630608293/500000000000 : ℝ)*(sp_s1_0) + (2625261286459/1000000000000 : ℝ)*(sp_s1_1) + (328157637807/125000000000 : ℝ)*(sp_s1_2) + (249999971591/250000000000 : ℝ)*(sp_s1_6) + (2625261309027/1000000000000 : ℝ)*(f.sum) + (7140423777052454111/20869709850000000000000000000000 : ℝ)*base63 + (6880919734021/8545000000000000000000000 : ℝ)*base65 + (642972204999947/3330450000000000000000000000 : ℝ)*base66 + (35460061286233/187990000000000000000000000 : ℝ)*base69 + (4024565476700679/6049689100000000000000000000 : ℝ)*base71 + (87578970435799/353990000000000000000000000 : ℝ)*base72 + (480902883856829/1110150000000000000000000000 : ℝ)*base75 + (27394648102173/44248750000000000000000000 : ℝ)*base77 + (60519513147375432973/117894599550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c318077_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-666921711/1250000000 : ℝ)*x 0 + (3587217291/10000000000 : ℝ)*x 1 + (3505902107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666921711/1250000000 : ℝ)^79 ≤ (45485542008617/100000000000000 : ℝ)^63 := by
    have hnat : (666921711 : ℕ)^79*100000000000000^63 ≤ 45485542008617^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666921711 1250000000 45485542008617 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3587217291/10000000000 : ℝ)^79 ≤ (27649053622919/100000000000000 : ℝ)^63 := by
    have hnat : (3587217291 : ℕ)^79*100000000000000^63 ≤ 27649053622919^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3587217291 10000000000 27649053622919 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3505902107/10000000000 : ℝ)^79 ≤ (5373080872487/20000000000000 : ℝ)^63 := by
    have hnat : (3505902107 : ℕ)^79*20000000000000^63 ≤ 5373080872487^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505902107 10000000000 5373080872487 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-666921711/1250000000 : ℝ), (3587217291/10000000000 : ℝ), (3505902107/10000000000 : ℝ)] ![(45485542008617/100000000000000 : ℝ), (27649053622919/100000000000000 : ℝ), (5373080872487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-666921711/1250000000 : ℝ)|^79 ≤ (45485542008617/100000000000000 : ℝ)^63
        have hw : |(-666921711/1250000000 : ℝ)|=(666921711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3587217291/10000000000 : ℝ)|^79 ≤ (27649053622919/100000000000000 : ℝ)^63
        have hw : |(3587217291/10000000000 : ℝ)|=(3587217291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3505902107/10000000000 : ℝ)|^79 ≤ (5373080872487/20000000000000 : ℝ)^63
        have hw : |(3505902107/10000000000 : ℝ)|=(3505902107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318077_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3620885727/10000000000 : ℝ)*x 0 + (-458967729/2000000000 : ℝ)*x 1 + (6318796727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3620885727/10000000000 : ℝ)^79 ≤ (3496856429671/12500000000000 : ℝ)^63 := by
    have hnat : (3620885727 : ℕ)^79*12500000000000^63 ≤ 3496856429671^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3620885727 10000000000 3496856429671 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458967729/2000000000 : ℝ)^79 ≤ (3947694206997/25000000000000 : ℝ)^63 := by
    have hnat : (458967729 : ℕ)^79*25000000000000^63 ≤ 3947694206997^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458967729 2000000000 3947694206997 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6318796727/10000000000 : ℝ)^79 ≤ (7029296463667/12500000000000 : ℝ)^63 := by
    have hnat : (6318796727 : ℕ)^79*12500000000000^63 ≤ 7029296463667^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6318796727 10000000000 7029296463667 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3620885727/10000000000 : ℝ), (-458967729/2000000000 : ℝ), (6318796727/10000000000 : ℝ)] ![(3496856429671/12500000000000 : ℝ), (3947694206997/25000000000000 : ℝ), (7029296463667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3620885727/10000000000 : ℝ)|^79 ≤ (3496856429671/12500000000000 : ℝ)^63
        have hw : |(3620885727/10000000000 : ℝ)|=(3620885727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458967729/2000000000 : ℝ)|^79 ≤ (3947694206997/25000000000000 : ℝ)^63
        have hw : |(-458967729/2000000000 : ℝ)|=(458967729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6318796727/10000000000 : ℝ)|^79 ≤ (7029296463667/12500000000000 : ℝ)^63
        have hw : |(6318796727/10000000000 : ℝ)|=(6318796727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318077_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4174060433/10000000000 : ℝ)*x 0 + (5459661343/10000000000 : ℝ)*x 1 + (-137139853/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174060433/10000000000 : ℝ)^79 ≤ (33434335523611/100000000000000 : ℝ)^63 := by
    have hnat : (4174060433 : ℕ)^79*100000000000000^63 ≤ 33434335523611^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174060433 10000000000 33434335523611 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459661343/10000000000 : ℝ)^79 ≤ (46818138025953/100000000000000 : ℝ)^63 := by
    have hnat : (5459661343 : ℕ)^79*100000000000000^63 ≤ 46818138025953^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459661343 10000000000 46818138025953 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137139853/500000000 : ℝ)^79 ≤ (9873763218617/50000000000000 : ℝ)^63 := by
    have hnat : (137139853 : ℕ)^79*50000000000000^63 ≤ 9873763218617^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137139853 500000000 9873763218617 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174060433/10000000000 : ℝ), (5459661343/10000000000 : ℝ), (-137139853/500000000 : ℝ)] ![(33434335523611/100000000000000 : ℝ), (46818138025953/100000000000000 : ℝ), (9873763218617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174060433/10000000000 : ℝ)|^79 ≤ (33434335523611/100000000000000 : ℝ)^63
        have hw : |(4174060433/10000000000 : ℝ)|=(4174060433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459661343/10000000000 : ℝ)|^79 ≤ (46818138025953/100000000000000 : ℝ)^63
        have hw : |(5459661343/10000000000 : ℝ)|=(5459661343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137139853/500000000 : ℝ)|^79 ≤ (9873763218617/50000000000000 : ℝ)^63
        have hw : |(-137139853/500000000 : ℝ)|=(137139853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318077_s0_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1985298727/10000000000 : ℝ)*x 0 + (6686186093/10000000000 : ℝ)*x 1 + (1732269401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985298727/10000000000 : ℝ)^79 ≤ (6583637786339/50000000000000 : ℝ)^63 := by
    have hnat : (1985298727 : ℕ)^79*50000000000000^63 ≤ 6583637786339^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985298727 10000000000 6583637786339 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6686186093/10000000000 : ℝ)^79 ≤ (60364184608499/100000000000000 : ℝ)^63 := by
    have hnat : (6686186093 : ℕ)^79*100000000000000^63 ≤ 60364184608499^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6686186093 10000000000 60364184608499 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732269401/5000000000 : ℝ)^79 ≤ (26468539811519/100000000000000 : ℝ)^63 := by
    have hnat : (1732269401 : ℕ)^79*100000000000000^63 ≤ 26468539811519^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732269401 5000000000 26468539811519 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1985298727/10000000000 : ℝ), (6686186093/10000000000 : ℝ), (1732269401/5000000000 : ℝ)] ![(6583637786339/50000000000000 : ℝ), (60364184608499/100000000000000 : ℝ), (26468539811519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1985298727/10000000000 : ℝ)|^79 ≤ (6583637786339/50000000000000 : ℝ)^63
        have hw : |(1985298727/10000000000 : ℝ)|=(1985298727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6686186093/10000000000 : ℝ)|^79 ≤ (60364184608499/100000000000000 : ℝ)^63
        have hw : |(6686186093/10000000000 : ℝ)|=(6686186093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1732269401/5000000000 : ℝ)|^79 ≤ (26468539811519/100000000000000 : ℝ)^63
        have hw : |(1732269401/5000000000 : ℝ)|=(1732269401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318077 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-666921711/1250000000 : ℝ)*X 0 0+(3587217291/10000000000 : ℝ)*X 0 1+(3505902107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3620885727/10000000000 : ℝ)*X 1 0+(-458967729/2000000000 : ℝ)*X 1 1+(6318796727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318077_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4174060433/10000000000 : ℝ)*X 2 0+(5459661343/10000000000 : ℝ)*X 2 1+(-137139853/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1985298727/10000000000 : ℝ)*X 0 0+(6686186093/10000000000 : ℝ)*X 0 1+(1732269401/5000000000 : ℝ)*X 0 2+(1985298727/10000000000 : ℝ)*X 1 0+(6686186093/10000000000 : ℝ)*X 1 1+(1732269401/5000000000 : ℝ)*X 1 2+(1985298727/10000000000 : ℝ)*X 2 0+(6686186093/10000000000 : ℝ)*X 2 1+(1732269401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318077_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-19711840241463681615999/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (315649/1000000000000 : ℝ)*(base8) + (9263/12500000000 : ℝ)*(base19) + (279179/1000000000000 : ℝ)*(base21) + (90097/125000000000 : ℝ)*(base29) + (322781/1000000000000 : ℝ)*(base40) + (624793610063/1000000000000 : ℝ)*(base49) + (69514512139/250000000000 : ℝ)*(base50) + (395761590457/1000000000000 : ℝ)*(base60) + (7299/4000 : ℝ)*(major_s0_0) + (7299/4000 : ℝ)*(major_s0_1) + (7299/4000 : ℝ)*(major_s0_2) + (2628245049871/1000000000000 : ℝ)*(sp_s0_0) + (16426528903/6250000000 : ℝ)*(sp_s0_1) + (2628245086341/1000000000000 : ℝ)*(sp_s0_2) + (124999909903/125000000000 : ℝ)*(sp_s0_6) + (2628245365521/1000000000000 : ℝ)*(f.sum) + (12603597/12500000000000000000 : ℝ)*base62 + (6776693207/10000000000000000000000 : ℝ)*base65 + (867818531/2000000000000000000000 : ℝ)*base67 + (1136743923/2500000000000000000000 : ℝ)*base69 + (802965221/1250000000000000000000 : ℝ)*base71 + (892329473/2500000000000000000000 : ℝ)*base73 + (3679438001/10000000000000000000000 : ℝ)*base74 + (766766341/2000000000000000000000 : ℝ)*base77 + (414218203/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p018_b034 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 76 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=76 ∨ c=77 := by omega
  rcases hc with rfl|rfl
  · exact collision_c318076 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318077 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 76 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
