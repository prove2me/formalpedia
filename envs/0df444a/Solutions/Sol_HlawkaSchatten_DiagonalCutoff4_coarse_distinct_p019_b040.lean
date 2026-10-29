-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b040
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:28:40.03755+00:00
-- url     : https://prove2.me/submissions/14aebd8c-34d4-4bd4-8e4f-35d83cd35253

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
theorem collision_support_c319080_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1602180033/5000000000 : ℝ)*x 0 + (552439187/1000000000 : ℝ)*x 1 + (90975711/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1602180033/5000000000 : ℝ)^5 ≤ (24108857969009/100000000000000 : ℝ)^4 := by
    have hnat : (1602180033 : ℕ)^5*100000000000000^4 ≤ 24108857969009^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602180033 5000000000 24108857969009 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552439187/1000000000 : ℝ)^5 ≤ (2976703747219/6250000000000 : ℝ)^4 := by
    have hnat : (552439187 : ℕ)^5*6250000000000^4 ≤ 2976703747219^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552439187 1000000000 2976703747219 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90975711/250000000 : ℝ)^5 ≤ (14131941028777/50000000000000 : ℝ)^4 := by
    have hnat : (90975711 : ℕ)^5*50000000000000^4 ≤ 14131941028777^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90975711 250000000 14131941028777 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1602180033/5000000000 : ℝ), (552439187/1000000000 : ℝ), (90975711/250000000 : ℝ)] ![(24108857969009/100000000000000 : ℝ), (2976703747219/6250000000000 : ℝ), (14131941028777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1602180033/5000000000 : ℝ)|^5 ≤ (24108857969009/100000000000000 : ℝ)^4
        have hw : |(-1602180033/5000000000 : ℝ)|=(1602180033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552439187/1000000000 : ℝ)|^5 ≤ (2976703747219/6250000000000 : ℝ)^4
        have hw : |(552439187/1000000000 : ℝ)|=(552439187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90975711/250000000 : ℝ)|^5 ≤ (14131941028777/50000000000000 : ℝ)^4
        have hw : |(90975711/250000000 : ℝ)|=(90975711/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-838374809/2000000000 : ℝ)*x 0 + (3262291821/10000000000 : ℝ)*x 1 + (4959119327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838374809/2000000000 : ℝ)^5 ≤ (6745905865183/20000000000000 : ℝ)^4 := by
    have hnat : (838374809 : ℕ)^5*20000000000000^4 ≤ 6745905865183^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838374809 2000000000 6745905865183 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3262291821/10000000000 : ℝ)^5 ≤ (197239319773/800000000000 : ℝ)^4 := by
    have hnat : (3262291821 : ℕ)^5*800000000000^4 ≤ 197239319773^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3262291821 10000000000 197239319773 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4959119327/10000000000 : ℝ)^5 ≤ (41615555687231/100000000000000 : ℝ)^4 := by
    have hnat : (4959119327 : ℕ)^5*100000000000000^4 ≤ 41615555687231^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4959119327 10000000000 41615555687231 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-838374809/2000000000 : ℝ), (3262291821/10000000000 : ℝ), (4959119327/10000000000 : ℝ)] ![(6745905865183/20000000000000 : ℝ), (197239319773/800000000000 : ℝ), (41615555687231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-838374809/2000000000 : ℝ)|^5 ≤ (6745905865183/20000000000000 : ℝ)^4
        have hw : |(-838374809/2000000000 : ℝ)|=(838374809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3262291821/10000000000 : ℝ)|^5 ≤ (197239319773/800000000000 : ℝ)^4
        have hw : |(3262291821/10000000000 : ℝ)|=(3262291821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4959119327/10000000000 : ℝ)|^5 ≤ (41615555687231/100000000000000 : ℝ)^4
        have hw : |(4959119327/10000000000 : ℝ)|=(4959119327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4224686529/10000000000 : ℝ)*x 0 + (5205223/5000000000 : ℝ)*x 1 + (7165083313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224686529/10000000000 : ℝ)^5 ≤ (34059879910863/100000000000000 : ℝ)^4 := by
    have hnat : (4224686529 : ℕ)^5*100000000000000^4 ≤ 34059879910863^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224686529 10000000000 34059879910863 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205223/5000000000 : ℝ)^5 ≤ (1869978743/10000000000000 : ℝ)^4 := by
    have hnat : (5205223 : ℕ)^5*10000000000000^4 ≤ 1869978743^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205223 5000000000 1869978743 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7165083313/10000000000 : ℝ)^5 ≤ (4120088767911/6250000000000 : ℝ)^4 := by
    have hnat : (7165083313 : ℕ)^5*6250000000000^4 ≤ 4120088767911^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7165083313 10000000000 4120088767911 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224686529/10000000000 : ℝ), (5205223/5000000000 : ℝ), (7165083313/10000000000 : ℝ)] ![(34059879910863/100000000000000 : ℝ), (1869978743/10000000000000 : ℝ), (4120088767911/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224686529/10000000000 : ℝ)|^5 ≤ (34059879910863/100000000000000 : ℝ)^4
        have hw : |(4224686529/10000000000 : ℝ)|=(4224686529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205223/5000000000 : ℝ)|^5 ≤ (1869978743/10000000000000 : ℝ)^4
        have hw : |(5205223/5000000000 : ℝ)|=(5205223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7165083313/10000000000 : ℝ)|^5 ≤ (4120088767911/6250000000000 : ℝ)^4
        have hw : |(7165083313/10000000000 : ℝ)|=(7165083313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (446165599/10000000000 : ℝ)*x 0 + (499423341/625000000 : ℝ)*x 1 + (-3021243361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446165599/10000000000 : ℝ)^5 ≤ (1025274382589/50000000000000 : ℝ)^4 := by
    have hnat : (446165599 : ℕ)^5*50000000000000^4 ≤ 1025274382589^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446165599 10000000000 1025274382589 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499423341/625000000 : ℝ)^5 ≤ (75550270367327/100000000000000 : ℝ)^4 := by
    have hnat : (499423341 : ℕ)^5*100000000000000^4 ≤ 75550270367327^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499423341 625000000 75550270367327 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021243361/10000000000 : ℝ)^5 ≤ (4479836171109/20000000000000 : ℝ)^4 := by
    have hnat : (3021243361 : ℕ)^5*20000000000000^4 ≤ 4479836171109^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021243361 10000000000 4479836171109 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(446165599/10000000000 : ℝ), (499423341/625000000 : ℝ), (-3021243361/10000000000 : ℝ)] ![(1025274382589/50000000000000 : ℝ), (75550270367327/100000000000000 : ℝ), (4479836171109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(446165599/10000000000 : ℝ)|^5 ≤ (1025274382589/50000000000000 : ℝ)^4
        have hw : |(446165599/10000000000 : ℝ)|=(446165599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499423341/625000000 : ℝ)|^5 ≤ (75550270367327/100000000000000 : ℝ)^4
        have hw : |(499423341/625000000 : ℝ)|=(499423341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3021243361/10000000000 : ℝ)|^5 ≤ (4479836171109/20000000000000 : ℝ)^4
        have hw : |(-3021243361/10000000000 : ℝ)|=(3021243361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (776048941/2500000000 : ℝ)*x 0 + (406805899/625000000 : ℝ)*x 1 + (2577583073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (776048941/2500000000 : ℝ)^5 ≤ (11585275924277/50000000000000 : ℝ)^4 := by
    have hnat : (776048941 : ℕ)^5*50000000000000^4 ≤ 11585275924277^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776048941 2500000000 11585275924277 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406805899/625000000 : ℝ)^5 ≤ (58463394897089/100000000000000 : ℝ)^4 := by
    have hnat : (406805899 : ℕ)^5*100000000000000^4 ≤ 58463394897089^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406805899 625000000 58463394897089 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577583073/10000000000 : ℝ)^5 ≤ (4591513309061/25000000000000 : ℝ)^4 := by
    have hnat : (2577583073 : ℕ)^5*25000000000000^4 ≤ 4591513309061^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577583073 10000000000 4591513309061 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(776048941/2500000000 : ℝ), (406805899/625000000 : ℝ), (2577583073/10000000000 : ℝ)] ![(11585275924277/50000000000000 : ℝ), (58463394897089/100000000000000 : ℝ), (4591513309061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(776048941/2500000000 : ℝ)|^5 ≤ (11585275924277/50000000000000 : ℝ)^4
        have hw : |(776048941/2500000000 : ℝ)|=(776048941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(406805899/625000000 : ℝ)|^5 ≤ (58463394897089/100000000000000 : ℝ)^4
        have hw : |(406805899/625000000 : ℝ)|=(406805899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577583073/10000000000 : ℝ)|^5 ≤ (4591513309061/25000000000000 : ℝ)^4
        have hw : |(2577583073/10000000000 : ℝ)|=(2577583073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-1191575551/2000000000 : ℝ)*x 0 + (4836381571/10000000000 : ℝ)*x 1 + (617701117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191575551/2000000000 : ℝ)^5 ≤ (327148175339/625000000000 : ℝ)^4 := by
    have hnat : (1191575551 : ℕ)^5*625000000000^4 ≤ 327148175339^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191575551 2000000000 327148175339 625000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4836381571/10000000000 : ℝ)^5 ≤ (20166043578861/50000000000000 : ℝ)^4 := by
    have hnat : (4836381571 : ℕ)^5*50000000000000^4 ≤ 20166043578861^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836381571 10000000000 20166043578861 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617701117/5000000000 : ℝ)^5 ≤ (1831051193063/25000000000000 : ℝ)^4 := by
    have hnat : (617701117 : ℕ)^5*25000000000000^4 ≤ 1831051193063^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617701117 5000000000 1831051193063 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1191575551/2000000000 : ℝ), (4836381571/10000000000 : ℝ), (617701117/5000000000 : ℝ)] ![(327148175339/625000000000 : ℝ), (20166043578861/50000000000000 : ℝ), (1831051193063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1191575551/2000000000 : ℝ)|^5 ≤ (327148175339/625000000000 : ℝ)^4
        have hw : |(-1191575551/2000000000 : ℝ)|=(1191575551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4836381571/10000000000 : ℝ)|^5 ≤ (20166043578861/50000000000000 : ℝ)^4
        have hw : |(4836381571/10000000000 : ℝ)|=(4836381571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617701117/5000000000 : ℝ)|^5 ≤ (1831051193063/25000000000000 : ℝ)^4
        have hw : |(617701117/5000000000 : ℝ)|=(617701117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2680811917/5000000000 : ℝ)*x 0 + (17728981/10000000000 : ℝ)*x 1 + (6115819097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680811917/5000000000 : ℝ)^5 ≤ (5734960609957/12500000000000 : ℝ)^4 := by
    have hnat : (2680811917 : ℕ)^5*12500000000000^4 ≤ 5734960609957^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680811917 5000000000 5734960609957 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17728981/10000000000 : ℝ)^5 ≤ (36379331831/100000000000000 : ℝ)^4 := by
    have hnat : (17728981 : ℕ)^5*100000000000000^4 ≤ 36379331831^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17728981 10000000000 36379331831 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6115819097/10000000000 : ℝ)^5 ≤ (54083935774099/100000000000000 : ℝ)^4 := by
    have hnat : (6115819097 : ℕ)^5*100000000000000^4 ≤ 54083935774099^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6115819097 10000000000 54083935774099 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680811917/5000000000 : ℝ), (17728981/10000000000 : ℝ), (6115819097/10000000000 : ℝ)] ![(5734960609957/12500000000000 : ℝ), (36379331831/100000000000000 : ℝ), (54083935774099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680811917/5000000000 : ℝ)|^5 ≤ (5734960609957/12500000000000 : ℝ)^4
        have hw : |(2680811917/5000000000 : ℝ)|=(2680811917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17728981/10000000000 : ℝ)|^5 ≤ (36379331831/100000000000000 : ℝ)^4
        have hw : |(17728981/10000000000 : ℝ)|=(17728981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6115819097/10000000000 : ℝ)|^5 ≤ (54083935774099/100000000000000 : ℝ)^4
        have hw : |(6115819097/10000000000 : ℝ)|=(6115819097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (92773469/1250000000 : ℝ)*x 0 + (2624218819/5000000000 : ℝ)*x 1 + (-183647443/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92773469/1250000000 : ℝ)^5 ≤ (9684612257/250000000000 : ℝ)^4 := by
    have hnat : (92773469 : ℕ)^5*250000000000^4 ≤ 9684612257^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92773469 1250000000 9684612257 250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624218819/5000000000 : ℝ)^5 ≤ (44672221665059/100000000000000 : ℝ)^4 := by
    have hnat : (2624218819 : ℕ)^5*100000000000000^4 ≤ 44672221665059^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624218819 5000000000 44672221665059 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183647443/312500000 : ℝ)^5 ≤ (12863483355377/25000000000000 : ℝ)^4 := by
    have hnat : (183647443 : ℕ)^5*25000000000000^4 ≤ 12863483355377^4*312500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183647443 312500000 12863483355377 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(92773469/1250000000 : ℝ), (2624218819/5000000000 : ℝ), (-183647443/312500000 : ℝ)] ![(9684612257/250000000000 : ℝ), (44672221665059/100000000000000 : ℝ), (12863483355377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(92773469/1250000000 : ℝ)|^5 ≤ (9684612257/250000000000 : ℝ)^4
        have hw : |(92773469/1250000000 : ℝ)|=(92773469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624218819/5000000000 : ℝ)|^5 ≤ (44672221665059/100000000000000 : ℝ)^4
        have hw : |(2624218819/5000000000 : ℝ)|=(2624218819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183647443/312500000 : ℝ)|^5 ≤ (12863483355377/25000000000000 : ℝ)^4
        have hw : |(-183647443/312500000 : ℝ)|=(183647443/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2680811917/5000000000 : ℝ)*x 0 + (5169470739/10000000000 : ℝ)*x 1 + (1621137291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680811917/5000000000 : ℝ)^5 ≤ (5734960609957/12500000000000 : ℝ)^4 := by
    have hnat : (2680811917 : ℕ)^5*12500000000000^4 ≤ 5734960609957^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680811917 5000000000 5734960609957 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169470739/10000000000 : ℝ)^5 ≤ (43833646586627/100000000000000 : ℝ)^4 := by
    have hnat : (5169470739 : ℕ)^5*100000000000000^4 ≤ 43833646586627^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169470739 10000000000 43833646586627 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1621137291/10000000000 : ℝ)^5 ≤ (5143334256561/50000000000000 : ℝ)^4 := by
    have hnat : (1621137291 : ℕ)^5*50000000000000^4 ≤ 5143334256561^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621137291 10000000000 5143334256561 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680811917/5000000000 : ℝ), (5169470739/10000000000 : ℝ), (1621137291/10000000000 : ℝ)] ![(5734960609957/12500000000000 : ℝ), (43833646586627/100000000000000 : ℝ), (5143334256561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680811917/5000000000 : ℝ)|^5 ≤ (5734960609957/12500000000000 : ℝ)^4
        have hw : |(2680811917/5000000000 : ℝ)|=(2680811917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169470739/10000000000 : ℝ)|^5 ≤ (43833646586627/100000000000000 : ℝ)^4
        have hw : |(5169470739/10000000000 : ℝ)|=(5169470739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1621137291/10000000000 : ℝ)|^5 ≤ (5143334256561/50000000000000 : ℝ)^4
        have hw : |(1621137291/10000000000 : ℝ)|=(1621137291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-152126921/625000000 : ℝ)*x 0 + (1816593299/2500000000 : ℝ)*x 1 + (457391711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152126921/625000000 : ℝ)^5 ≤ (17096514247759/100000000000000 : ℝ)^4 := by
    have hnat : (152126921 : ℕ)^5*100000000000000^4 ≤ 17096514247759^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152126921 625000000 17096514247759 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1816593299/2500000000 : ℝ)^5 ≤ (67088352036277/100000000000000 : ℝ)^4 := by
    have hnat : (1816593299 : ℕ)^5*100000000000000^4 ≤ 67088352036277^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816593299 2500000000 67088352036277 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457391711/2000000000 : ℝ)^5 ≤ (15815133702017/100000000000000 : ℝ)^4 := by
    have hnat : (457391711 : ℕ)^5*100000000000000^4 ≤ 15815133702017^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457391711 2000000000 15815133702017 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152126921/625000000 : ℝ), (1816593299/2500000000 : ℝ), (457391711/2000000000 : ℝ)] ![(17096514247759/100000000000000 : ℝ), (67088352036277/100000000000000 : ℝ), (15815133702017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152126921/625000000 : ℝ)|^5 ≤ (17096514247759/100000000000000 : ℝ)^4
        have hw : |(-152126921/625000000 : ℝ)|=(152126921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1816593299/2500000000 : ℝ)|^5 ≤ (67088352036277/100000000000000 : ℝ)^4
        have hw : |(1816593299/2500000000 : ℝ)|=(1816593299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457391711/2000000000 : ℝ)|^5 ≤ (15815133702017/100000000000000 : ℝ)^4
        have hw : |(457391711/2000000000 : ℝ)|=(457391711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (930096229/1250000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (3907396959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930096229/1250000000 : ℝ)^5 ≤ (69107047411661/100000000000000 : ℝ)^4 := by
    have hnat : (930096229 : ℕ)^5*100000000000000^4 ≤ 69107047411661^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930096229 1250000000 69107047411661 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^5 ≤ (0 : ℝ)^4 := by
    have hnat : (0 : ℕ)^5*1^4 ≤ 0^4*1^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3907396959/10000000000 : ℝ)^5 ≤ (247143620599/800000000000 : ℝ)^4 := by
    have hnat : (3907396959 : ℕ)^5*800000000000^4 ≤ 247143620599^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3907396959 10000000000 247143620599 800000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(930096229/1250000000 : ℝ), (0 : ℝ), (3907396959/10000000000 : ℝ)] ![(69107047411661/100000000000000 : ℝ), (0 : ℝ), (247143620599/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(930096229/1250000000 : ℝ)|^5 ≤ (69107047411661/100000000000000 : ℝ)^4
        have hw : |(930096229/1250000000 : ℝ)|=(930096229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^5 ≤ (0 : ℝ)^4
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3907396959/10000000000 : ℝ)|^5 ≤ (247143620599/800000000000 : ℝ)^4
        have hw : |(3907396959/10000000000 : ℝ)|=(3907396959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (181247399/5000000000 : ℝ)*x 0 + (82103247/100000000 : ℝ)*x 1 + (-2788608469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181247399/5000000000 : ℝ)^5 ≤ (316342264319/20000000000000 : ℝ)^4 := by
    have hnat : (181247399 : ℕ)^5*20000000000000^4 ≤ 316342264319^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181247399 5000000000 316342264319 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82103247/100000000 : ℝ)^5 ≤ (15630771404761/20000000000000 : ℝ)^4 := by
    have hnat : (82103247 : ℕ)^5*20000000000000^4 ≤ 15630771404761^4*100000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82103247 100000000 15630771404761 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2788608469/10000000000 : ℝ)^5 ≤ (20264431638409/100000000000000 : ℝ)^4 := by
    have hnat : (2788608469 : ℕ)^5*100000000000000^4 ≤ 20264431638409^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788608469 10000000000 20264431638409 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181247399/5000000000 : ℝ), (82103247/100000000 : ℝ), (-2788608469/10000000000 : ℝ)] ![(316342264319/20000000000000 : ℝ), (15630771404761/20000000000000 : ℝ), (20264431638409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181247399/5000000000 : ℝ)|^5 ≤ (316342264319/20000000000000 : ℝ)^4
        have hw : |(181247399/5000000000 : ℝ)|=(181247399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82103247/100000000 : ℝ)|^5 ≤ (15630771404761/20000000000000 : ℝ)^4
        have hw : |(82103247/100000000 : ℝ)|=(82103247/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2788608469/10000000000 : ℝ)|^5 ≤ (20264431638409/100000000000000 : ℝ)^4
        have hw : |(-2788608469/10000000000 : ℝ)|=(2788608469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s0_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (930096229/1250000000 : ℝ)*x 0 + (2668898593/10000000000 : ℝ)*x 1 + (1798233113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930096229/1250000000 : ℝ)^5 ≤ (69107047411661/100000000000000 : ℝ)^4 := by
    have hnat : (930096229 : ℕ)^5*100000000000000^4 ≤ 69107047411661^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930096229 1250000000 69107047411661 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2668898593/10000000000 : ℝ)^5 ≤ (19182936576161/100000000000000 : ℝ)^4 := by
    have hnat : (2668898593 : ℕ)^5*100000000000000^4 ≤ 19182936576161^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668898593 10000000000 19182936576161 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1798233113/10000000000 : ℝ)^5 ≤ (1463751999179/12500000000000 : ℝ)^4 := by
    have hnat : (1798233113 : ℕ)^5*12500000000000^4 ≤ 1463751999179^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798233113 10000000000 1463751999179 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(930096229/1250000000 : ℝ), (2668898593/10000000000 : ℝ), (1798233113/10000000000 : ℝ)] ![(69107047411661/100000000000000 : ℝ), (19182936576161/100000000000000 : ℝ), (1463751999179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(930096229/1250000000 : ℝ)|^5 ≤ (69107047411661/100000000000000 : ℝ)^4
        have hw : |(930096229/1250000000 : ℝ)|=(930096229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2668898593/10000000000 : ℝ)|^5 ≤ (19182936576161/100000000000000 : ℝ)^4
        have hw : |(2668898593/10000000000 : ℝ)|=(2668898593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1798233113/10000000000 : ℝ)|^5 ≤ (1463751999179/12500000000000 : ℝ)^4
        have hw : |(1798233113/10000000000 : ℝ)|=(1798233113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-3357072551/10000000000 : ℝ)*x 0 + (1345520287/2500000000 : ℝ)*x 1 + (3647676001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3357072551/10000000000 : ℝ)^5 ≤ (6388382590681/25000000000000 : ℝ)^4 := by
    have hnat : (3357072551 : ℕ)^5*25000000000000^4 ≤ 6388382590681^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357072551 10000000000 6388382590681 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345520287/2500000000 : ℝ)^5 ≤ (23049303487113/50000000000000 : ℝ)^4 := by
    have hnat : (1345520287 : ℕ)^5*50000000000000^4 ≤ 23049303487113^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345520287 2500000000 23049303487113 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3647676001/10000000000 : ℝ)^5 ≤ (28347862646847/100000000000000 : ℝ)^4 := by
    have hnat : (3647676001 : ℕ)^5*100000000000000^4 ≤ 28347862646847^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3647676001 10000000000 28347862646847 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3357072551/10000000000 : ℝ), (1345520287/2500000000 : ℝ), (3647676001/10000000000 : ℝ)] ![(6388382590681/25000000000000 : ℝ), (23049303487113/50000000000000 : ℝ), (28347862646847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3357072551/10000000000 : ℝ)|^5 ≤ (6388382590681/25000000000000 : ℝ)^4
        have hw : |(-3357072551/10000000000 : ℝ)|=(3357072551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1345520287/2500000000 : ℝ)|^5 ≤ (23049303487113/50000000000000 : ℝ)^4
        have hw : |(1345520287/2500000000 : ℝ)|=(1345520287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3647676001/10000000000 : ℝ)|^5 ≤ (28347862646847/100000000000000 : ℝ)^4
        have hw : |(3647676001/10000000000 : ℝ)|=(3647676001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2891103081/5000000000 : ℝ)*x 0 + (-152398617/2000000000 : ℝ)*x 1 + (2666553823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2891103081/5000000000 : ℝ)^5 ≤ (50421639759153/100000000000000 : ℝ)^4 := by
    have hnat : (2891103081 : ℕ)^5*100000000000000^4 ≤ 50421639759153^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891103081 5000000000 50421639759153 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152398617/2000000000 : ℝ)^5 ≤ (16013961463/400000000000 : ℝ)^4 := by
    have hnat : (152398617 : ℕ)^5*400000000000^4 ≤ 16013961463^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152398617 2000000000 16013961463 400000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2666553823/5000000000 : ℝ)^5 ≤ (1424214683231/3125000000000 : ℝ)^4 := by
    have hnat : (2666553823 : ℕ)^5*3125000000000^4 ≤ 1424214683231^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666553823 5000000000 1424214683231 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2891103081/5000000000 : ℝ), (-152398617/2000000000 : ℝ), (2666553823/5000000000 : ℝ)] ![(50421639759153/100000000000000 : ℝ), (16013961463/400000000000 : ℝ), (1424214683231/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2891103081/5000000000 : ℝ)|^5 ≤ (50421639759153/100000000000000 : ℝ)^4
        have hw : |(2891103081/5000000000 : ℝ)|=(2891103081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152398617/2000000000 : ℝ)|^5 ≤ (16013961463/400000000000 : ℝ)^4
        have hw : |(-152398617/2000000000 : ℝ)|=(152398617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2666553823/5000000000 : ℝ)|^5 ≤ (1424214683231/3125000000000 : ℝ)^4
        have hw : |(2666553823/5000000000 : ℝ)|=(2666553823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (784854079/2500000000 : ℝ)*x 0 + (231322569/400000000 : ℝ)*x 1 + (-1705589227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784854079/2500000000 : ℝ)^5 ≤ (4699927238061/20000000000000 : ℝ)^4 := by
    have hnat : (784854079 : ℕ)^5*20000000000000^4 ≤ 4699927238061^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784854079 2500000000 4699927238061 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231322569/400000000 : ℝ)^5 ≤ (10086198593623/20000000000000 : ℝ)^4 := by
    have hnat : (231322569 : ℕ)^5*20000000000000^4 ≤ 10086198593623^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231322569 400000000 10086198593623 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705589227/5000000000 : ℝ)^5 ≤ (26069370831513/100000000000000 : ℝ)^4 := by
    have hnat : (1705589227 : ℕ)^5*100000000000000^4 ≤ 26069370831513^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705589227 5000000000 26069370831513 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(784854079/2500000000 : ℝ), (231322569/400000000 : ℝ), (-1705589227/5000000000 : ℝ)] ![(4699927238061/20000000000000 : ℝ), (10086198593623/20000000000000 : ℝ), (26069370831513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(784854079/2500000000 : ℝ)|^5 ≤ (4699927238061/20000000000000 : ℝ)^4
        have hw : |(784854079/2500000000 : ℝ)|=(784854079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231322569/400000000 : ℝ)|^5 ≤ (10086198593623/20000000000000 : ℝ)^4
        have hw : |(231322569/400000000 : ℝ)|=(231322569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1705589227/5000000000 : ℝ)|^5 ≤ (26069370831513/100000000000000 : ℝ)^4
        have hw : |(-1705589227/5000000000 : ℝ)|=(1705589227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319080_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3929936849/10000000000 : ℝ)*x 0 + (4877317979/10000000000 : ℝ)*x 1 + (3624702349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3929936849/10000000000 : ℝ)^5 ≤ (31115871161207/100000000000000 : ℝ)^4 := by
    have hnat : (3929936849 : ℕ)^5*100000000000000^4 ≤ 31115871161207^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929936849 10000000000 31115871161207 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4877317979/10000000000 : ℝ)^5 ≤ (40759264463307/100000000000000 : ℝ)^4 := by
    have hnat : (4877317979 : ℕ)^5*100000000000000^4 ≤ 40759264463307^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877317979 10000000000 40759264463307 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3624702349/10000000000 : ℝ)^5 ≤ (7031216089167/25000000000000 : ℝ)^4 := by
    have hnat : (3624702349 : ℕ)^5*25000000000000^4 ≤ 7031216089167^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624702349 10000000000 7031216089167 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3929936849/10000000000 : ℝ), (4877317979/10000000000 : ℝ), (3624702349/10000000000 : ℝ)] ![(31115871161207/100000000000000 : ℝ), (40759264463307/100000000000000 : ℝ), (7031216089167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3929936849/10000000000 : ℝ)|^5 ≤ (31115871161207/100000000000000 : ℝ)^4
        have hw : |(3929936849/10000000000 : ℝ)|=(3929936849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4877317979/10000000000 : ℝ)|^5 ≤ (40759264463307/100000000000000 : ℝ)^4
        have hw : |(4877317979/10000000000 : ℝ)|=(4877317979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3624702349/10000000000 : ℝ)|^5 ≤ (7031216089167/25000000000000 : ℝ)^4
        have hw : |(3624702349/10000000000 : ℝ)|=(3624702349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319080 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1602180033/5000000000 : ℝ)*X 0 0+(552439187/1000000000 : ℝ)*X 0 1+(90975711/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-838374809/2000000000 : ℝ)*X 0 0+(3262291821/10000000000 : ℝ)*X 0 1+(4959119327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4224686529/10000000000 : ℝ)*X 1 0+(5205223/5000000000 : ℝ)*X 1 1+(7165083313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((446165599/10000000000 : ℝ)*X 2 0+(499423341/625000000 : ℝ)*X 2 1+(-3021243361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((776048941/2500000000 : ℝ)*X 0 0+(406805899/625000000 : ℝ)*X 0 1+(2577583073/10000000000 : ℝ)*X 0 2+(776048941/2500000000 : ℝ)*X 1 0+(406805899/625000000 : ℝ)*X 1 1+(2577583073/10000000000 : ℝ)*X 1 2+(776048941/2500000000 : ℝ)*X 2 0+(406805899/625000000 : ℝ)*X 2 1+(2577583073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1191575551/2000000000 : ℝ)*X 0 0+(4836381571/10000000000 : ℝ)*X 0 1+(617701117/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2680811917/5000000000 : ℝ)*X 1 0+(17728981/10000000000 : ℝ)*X 1 1+(6115819097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((92773469/1250000000 : ℝ)*X 2 0+(2624218819/5000000000 : ℝ)*X 2 1+(-183647443/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2680811917/5000000000 : ℝ)*X 0 0+(5169470739/10000000000 : ℝ)*X 0 1+(1621137291/10000000000 : ℝ)*X 0 2+(2680811917/5000000000 : ℝ)*X 1 0+(5169470739/10000000000 : ℝ)*X 1 1+(1621137291/10000000000 : ℝ)*X 1 2+(2680811917/5000000000 : ℝ)*X 2 0+(5169470739/10000000000 : ℝ)*X 2 1+(1621137291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-152126921/625000000 : ℝ)*X 0 0+(1816593299/2500000000 : ℝ)*X 0 1+(457391711/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((930096229/1250000000 : ℝ)*X 1 0+(3907396959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((181247399/5000000000 : ℝ)*X 2 0+(82103247/100000000 : ℝ)*X 2 1+(-2788608469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((930096229/1250000000 : ℝ)*X 0 0+(2668898593/10000000000 : ℝ)*X 0 1+(1798233113/10000000000 : ℝ)*X 0 2+(930096229/1250000000 : ℝ)*X 1 0+(2668898593/10000000000 : ℝ)*X 1 1+(1798233113/10000000000 : ℝ)*X 1 2+(930096229/1250000000 : ℝ)*X 2 0+(2668898593/10000000000 : ℝ)*X 2 1+(1798233113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((16877/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16877/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2186029469138058396267/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602997720883/500000000000 : ℝ)*(base7) + (368614577737/1000000000000 : ℝ)*(base49) + (731071/250000000000 : ℝ)*(base53) + (665753/1000000000000 : ℝ)*(base60) + (2074992553361/1000000000000 : ℝ)*(major_s0_0) + (2074992553361/1000000000000 : ℝ)*(major_s0_1) + (2074989629077/1000000000000 : ℝ)*(major_s0_2) + (3502453/500000000000 : ℝ)*(sp_s0_0) + (117202060871/50000000000 : ℝ)*(sp_s0_7) + (2344045189611/1000000000000 : ℝ)*(sp_s0_8) + (2344019592511/1000000000000 : ℝ)*(sp_s0_9) + (2327043424607/1000000000000 : ℝ)*(sp_s0_13) + (1516357/500000000000 : ℝ)*(sp_s0_15) + (15777049/500000000000 : ℝ)*(sp_s0_23) + (560523991421/500000000000 : ℝ)*(f.failure) + (234405114661/100000000000 : ℝ)*(f.sum) + (2093604676375167/5000000000000000000000000000 : ℝ)*base62 + (9631765346891619/10000000000000000000000000000 : ℝ)*base65 + (1189523414448331/10000000000000000000000000000 : ℝ)*base67 + (4066688472482633/10000000000000000000000000000 : ℝ)*base69 + (1021754592680411/1250000000000000000000000000 : ℝ)*base71 + (8063923404232967/10000000000000000000000000000 : ℝ)*base73 + (3197622742767033/10000000000000000000000000000 : ℝ)*base75 + (11910480590551669/10000000000000000000000000000 : ℝ)*base77 + (457273478159351/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (14287/25000000000000000 : ℝ)*base87 + (14287/25000000000000000 : ℝ)*base89 + (14287/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((7773/20000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(7773/20000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1619859393653180900199/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81706233537/125000000000 : ℝ)*(base3) + (137443906597/250000000000 : ℝ)*(base7) + (10741659/1000000000000 : ℝ)*(base8) + (9962829/1000000000000 : ℝ)*(base24) + (896952513491/1000000000000 : ℝ)*(base49) + (198007/1000000000000 : ℝ)*(base60) + (324956118507/200000000000 : ℝ)*(major_s0_0) + (324956118507/200000000000 : ℝ)*(major_s0_1) + (324956118507/200000000000 : ℝ)*(major_s0_2) + (2623917/1000000000000 : ℝ)*(sp_s0_7) + (205951432599/100000000000 : ℝ)*(sp_s0_14) + (1356588779931/500000000000 : ℝ)*(sp_s0_15) + (2059517728737/1000000000000 : ℝ)*(sp_s0_16) + (386969756777/500000000000 : ℝ)*(sp_s0_20) + (438906877731/500000000000 : ℝ)*(f.failure) + (1029763845783/500000000000 : ℝ)*(f.sum) + (419016456938637/1000000000000000000000000000 : ℝ)*base63 + (867627088955171/2000000000000000000000000000 : ℝ)*base64 + (454129146322103/2000000000000000000000000000 : ℝ)*base66 + (925899789077897/2000000000000000000000000000 : ℝ)*base68 + (17179246058267/500000000000000000000000000 : ℝ)*base70 + (1244090543955171/2000000000000000000000000000 : ℝ)*base72 + (280289873644829/2000000000000000000000000000 : ℝ)*base74 + (783600322677897/2000000000000000000000000000 : ℝ)*base76 + (170135760761363/1000000000000000000000000000 : ℝ)*base79 + (4143/25000000000000000 : ℝ)*base86 + (4143/25000000000000000 : ℝ)*base88 + (4143/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18241/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18241/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6707648394980848036149/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18741215103/200000000000 : ℝ)*(base3) + (1174656757277/1000000000000 : ℝ)*(base7) + (23707140563/250000000000 : ℝ)*(base40) + (3567497/1000000000000 : ℝ)*(base43) + (43529819439/1000000000000 : ℝ)*(base49) + (922141144333/500000000000 : ℝ)*(major_s0_0) + (1844278721169/1000000000000 : ℝ)*(major_s0_1) + (922141144333/500000000000 : ℝ)*(major_s0_2) + (4160253/62500000000 : ℝ)*(sp_s0_9) + (51903/5000000000 : ℝ)*(sp_s0_14) + (101252887807/50000000000 : ℝ)*(sp_s0_21) + (264847222469/125000000000 : ℝ)*(sp_s0_22) + (506250393173/250000000000 : ℝ)*(sp_s0_23) + (207735374651/100000000000 : ℝ)*(sp_s0_27) + (996403064749/1000000000000 : ℝ)*(f.failure) + (2025071704237/1000000000000 : ℝ)*(f.sum) + (2675438632176571/10000000000000000000000000000 : ℝ)*base63 + (2252206053708651/5000000000000000000000000000 : ℝ)*base65 + (2779202213324299/10000000000000000000000000000 : ℝ)*base67 + (3971615015548257/5000000000000000000000000000 : ℝ)*base69 + (873664520314227/1250000000000000000000000000 : ℝ)*base71 + (84170610291349/5000000000000000000000000000 : ℝ)*base72 + (3533967609080057/10000000000000000000000000000 : ℝ)*base75 + (4337747648548257/5000000000000000000000000000 : ℝ)*base77 + (3523727233258399/10000000000000000000000000000 : ℝ)*base78 + (25703/50000000000000000 : ℝ)*base87 + (25703/50000000000000000 : ℝ)*base89 + (25703/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (16877/25000 : ℝ) ^ (79/16 : ℝ) ≤ (3592373753204720837/25000000000000000000 : ℝ) := by
    have hpowers : (16877/25000 : ℝ)^79 ≤ (3592373753204720837/25000000000000000000 : ℝ)^16 := by
      have hnat : (16877 : ℕ)^79*25000000000000000000^16 ≤ 3592373753204720837^16*25000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16877 25000 3592373753204720837 25000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16877/25000 : ℝ)) (X := (3592373753204720837/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (28592373753204720837/25000000000000000000 : ℝ) ≤ (10275658474697033/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (28592373753204720837/25000000000000000000 : ℝ)^16 ≤ (10275658474697033/10000000000000000 : ℝ)^79 := by
      have hnat : (28592373753204720837 : ℕ)^16*10000000000000000^79 ≤ 10275658474697033^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28592373753204720837 25000000000000000000 10275658474697033 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10275658474697033/10000000000000000 : ℝ)) (X := (28592373753204720837/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (16092373753204720837/12500000000000000000 : ℝ) ≤ (10524943342237073/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (16092373753204720837/12500000000000000000 : ℝ)^16 ≤ (10524943342237073/10000000000000000 : ℝ)^79 := by
      have hnat : (16092373753204720837 : ℕ)^16*10000000000000000^79 ≤ 10524943342237073^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16092373753204720837 12500000000000000000 10524943342237073 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10524943342237073/10000000000000000 : ℝ)) (X := (16092373753204720837/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(275658474697033/6750800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6232121688501/168770000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (16877/25000 : ℝ)) (alpha := (275658474697033/6750800000000000 : ℝ)) (beta := (6232121688501/168770000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16877/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(275658474697033/6750800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6232121688501/168770000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7773/20000 : ℝ) ^ (79/16 : ℝ) ≤ (235172183718489137/25000000000000000000 : ℝ) := by
    have hpowers : (7773/20000 : ℝ)^79 ≤ (235172183718489137/25000000000000000000 : ℝ)^16 := by
      have hnat : (7773 : ℕ)^79*25000000000000000000^16 ≤ 235172183718489137^16*20000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7773 20000 235172183718489137 25000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7773/20000 : ℝ)) (X := (235172183718489137/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25235172183718489137/25000000000000000000 : ℝ) ≤ (5009490431510149/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (25235172183718489137/25000000000000000000 : ℝ)^16 ≤ (5009490431510149/5000000000000000 : ℝ)^79 := by
      have hnat : (25235172183718489137 : ℕ)^16*5000000000000000^79 ≤ 5009490431510149^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25235172183718489137 25000000000000000000 5009490431510149 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009490431510149/5000000000000000 : ℝ)) (X := (25235172183718489137/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12735172183718489137/12500000000000000000 : ℝ) ≤ (5018910592193189/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (12735172183718489137/12500000000000000000 : ℝ)^16 ≤ (5018910592193189/5000000000000000 : ℝ)^79 := by
      have hnat : (12735172183718489137 : ℕ)^16*5000000000000000^79 ≤ 5018910592193189^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12735172183718489137 12500000000000000000 5018910592193189 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018910592193189/5000000000000000 : ℝ)) (X := (12735172183718489137/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(9490431510149/1943250000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(58876004269/12145312500000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (7773/20000 : ℝ)) (alpha := (9490431510149/1943250000000000 : ℝ)) (beta := (58876004269/12145312500000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (7773/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(9490431510149/1943250000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(58876004269/12145312500000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (18241/25000 : ℝ) ^ (79/16 : ℝ) ≤ (21091083141733976479/100000000000000000000 : ℝ) := by
    have hpowers : (18241/25000 : ℝ)^79 ≤ (21091083141733976479/100000000000000000000 : ℝ)^16 := by
      have hnat : (18241 : ℕ)^79*100000000000000000000^16 ≤ 21091083141733976479^16*25000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18241 25000 21091083141733976479 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18241/25000 : ℝ)) (X := (21091083141733976479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (121091083141733976479/100000000000000000000 : ℝ) ≤ (10395199854053421/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (121091083141733976479/100000000000000000000 : ℝ)^16 ≤ (10395199854053421/10000000000000000 : ℝ)^79 := by
      have hnat : (121091083141733976479 : ℕ)^16*10000000000000000^79 ≤ 10395199854053421^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121091083141733976479 100000000000000000000 10395199854053421 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10395199854053421/10000000000000000 : ℝ)) (X := (121091083141733976479/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (71091083141733976479/50000000000000000000 : ℝ) ≤ (2147761092573053/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (71091083141733976479/50000000000000000000 : ℝ)^16 ≤ (2147761092573053/2000000000000000 : ℝ)^79 := by
      have hnat : (71091083141733976479 : ℕ)^16*2000000000000000^79 ≤ 2147761092573053^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71091083141733976479 50000000000000000000 2147761092573053 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2147761092573053/2000000000000000 : ℝ)) (X := (71091083141733976479/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(395199854053421/7296400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(85901402202961/1824100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (18241/25000 : ℝ)) (alpha := (395199854053421/7296400000000000 : ℝ)) (beta := (85901402202961/1824100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (18241/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(395199854053421/7296400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(85901402202961/1824100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3357072551/10000000000 : ℝ)*X 0 0+(1345520287/2500000000 : ℝ)*X 0 1+(3647676001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2891103081/5000000000 : ℝ)*X 1 0+(-152398617/2000000000 : ℝ)*X 1 1+(2666553823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((784854079/2500000000 : ℝ)*X 2 0+(231322569/400000000 : ℝ)*X 2 1+(-1705589227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3929936849/10000000000 : ℝ)*X 0 0+(4877317979/10000000000 : ℝ)*X 0 1+(3624702349/10000000000 : ℝ)*X 0 2+(3929936849/10000000000 : ℝ)*X 1 0+(4877317979/10000000000 : ℝ)*X 1 1+(3624702349/10000000000 : ℝ)*X 1 2+(3929936849/10000000000 : ℝ)*X 2 0+(4877317979/10000000000 : ℝ)*X 2 1+(3624702349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319080_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-644855191879768770304397428032076887/79764804798700000000000000000000000 : ℝ) := by norm_num
    linear_combination (293/250000000000 : ℝ)*(base7) + (5791/250000000000 : ℝ)*(base13) + (13669/1000000000000 : ℝ)*(base15) + (6419/200000000000 : ℝ)*(base23) + (119642805379/1000000000000 : ℝ)*(base40) + (549702553847/500000000000 : ℝ)*(base49) + (248223698651/500000000000 : ℝ)*(base50) + (925470003307/500000000000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (92547/50000 : ℝ)*(major_s1_2) + (2694819202691/1000000000000 : ℝ)*(sp_s1_0) + (673704801393/250000000000 : ℝ)*(sp_s1_1) + (1347409593573/500000000000 : ℝ)*(sp_s1_2) + (1000000007787/1000000000000 : ℝ)*(sp_s1_6) + (2694819219241/1000000000000 : ℝ)*(f.sum) + (77246135802246941/236312155000000000000000000000 : ℝ)*base62 + (25846551627581/182410000000000000000000000 : ℝ)*base64 + (4840762436393/12955000000000000000000000 : ℝ)*base67 + (48002469442307/182410000000000000000000000 : ℝ)*base68 + (22070744483570152849/61570671400000000000000000000000 : ℝ)*base70 + (10495478222861/168770000000000000000000000 : ℝ)*base72 + (13188019921709/25910000000000000000000000 : ℝ)*base74 + (720534753097289/3375400000000000000000000000 : ℝ)*base76 + (21653530812884521/437283070000000000000000000000 : ℝ)*base79 + (3307/500000000000 : ℝ)*base81 + (3307/500000000000 : ℝ)*base86 + (1323/200000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p019_b040 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 80 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=80 := by omega
  rcases hc with rfl
  · exact collision_c319080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 80 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b040 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
