-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b031
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:20:45.144691+00:00
-- url     : https://prove2.me/submissions/67b7a1e0-8e68-467d-8445-e89029677500

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
theorem collision_support_c318070_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-267940137/1250000000 : ℝ)*x 0 + (-800052481/2000000000 : ℝ)*x 1 + (-610020703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267940137/1250000000 : ℝ)^79 ≤ (7248121287013/50000000000000 : ℝ)^63 := by
    have hnat : (267940137 : ℕ)^79*50000000000000^63 ≤ 7248121287013^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267940137 1250000000 7248121287013 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800052481/2000000000 : ℝ)^79 ≤ (6339595997109/20000000000000 : ℝ)^63 := by
    have hnat : (800052481 : ℕ)^79*20000000000000^63 ≤ 6339595997109^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800052481 2000000000 6339595997109 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610020703/1000000000 : ℝ)^79 ≤ (53805777426787/100000000000000 : ℝ)^63 := by
    have hnat : (610020703 : ℕ)^79*100000000000000^63 ≤ 53805777426787^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610020703 1000000000 53805777426787 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267940137/1250000000 : ℝ), (-800052481/2000000000 : ℝ), (-610020703/1000000000 : ℝ)] ![(7248121287013/50000000000000 : ℝ), (6339595997109/20000000000000 : ℝ), (53805777426787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267940137/1250000000 : ℝ)|^79 ≤ (7248121287013/50000000000000 : ℝ)^63
        have hw : |(-267940137/1250000000 : ℝ)|=(267940137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-800052481/2000000000 : ℝ)|^79 ≤ (6339595997109/20000000000000 : ℝ)^63
        have hw : |(-800052481/2000000000 : ℝ)|=(800052481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-610020703/1000000000 : ℝ)|^79 ≤ (53805777426787/100000000000000 : ℝ)^63
        have hw : |(-610020703/1000000000 : ℝ)|=(610020703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318070_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1525051729/2500000000 : ℝ)*x 0 + (500032809/1250000000 : ℝ)*x 1 + (-1071760583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1525051729/2500000000 : ℝ)^79 ≤ (26902888082951/50000000000000 : ℝ)^63 := by
    have hnat : (1525051729 : ℕ)^79*50000000000000^63 ≤ 26902888082951^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525051729 2500000000 26902888082951 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500032809/1250000000 : ℝ)^79 ≤ (6339596130257/20000000000000 : ℝ)^63 := by
    have hnat : (500032809 : ℕ)^79*20000000000000^63 ≤ 6339596130257^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500032809 1250000000 6339596130257 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071760583/5000000000 : ℝ)^79 ≤ (14496243167651/100000000000000 : ℝ)^63 := by
    have hnat : (1071760583 : ℕ)^79*100000000000000^63 ≤ 14496243167651^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071760583 5000000000 14496243167651 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1525051729/2500000000 : ℝ), (500032809/1250000000 : ℝ), (-1071760583/5000000000 : ℝ)] ![(26902888082951/50000000000000 : ℝ), (6339596130257/20000000000000 : ℝ), (14496243167651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1525051729/2500000000 : ℝ)|^79 ≤ (26902888082951/50000000000000 : ℝ)^63
        have hw : |(1525051729/2500000000 : ℝ)|=(1525051729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500032809/1250000000 : ℝ)|^79 ≤ (6339596130257/20000000000000 : ℝ)^63
        have hw : |(500032809/1250000000 : ℝ)|=(500032809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071760583/5000000000 : ℝ)|^79 ≤ (14496243167651/100000000000000 : ℝ)^63
        have hw : |(-1071760583/5000000000 : ℝ)|=(1071760583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318070_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3736250257/10000000000 : ℝ)*x 0 + (-311766709/625000000 : ℝ)*x 1 + (3736250317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3736250257/10000000000 : ℝ)^79 ≤ (7274250848251/25000000000000 : ℝ)^63 := by
    have hnat : (3736250257 : ℕ)^79*25000000000000^63 ≤ 7274250848251^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736250257 10000000000 7274250848251 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311766709/625000000 : ℝ)^79 ≤ (41805992599979/100000000000000 : ℝ)^63 := by
    have hnat : (311766709 : ℕ)^79*100000000000000^63 ≤ 41805992599979^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311766709 625000000 41805992599979 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3736250317/10000000000 : ℝ)^79 ≤ (29097003978939/100000000000000 : ℝ)^63 := by
    have hnat : (3736250317 : ℕ)^79*100000000000000^63 ≤ 29097003978939^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736250317 10000000000 29097003978939 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3736250257/10000000000 : ℝ), (-311766709/625000000 : ℝ), (3736250317/10000000000 : ℝ)] ![(7274250848251/25000000000000 : ℝ), (41805992599979/100000000000000 : ℝ), (29097003978939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3736250257/10000000000 : ℝ)|^79 ≤ (7274250848251/25000000000000 : ℝ)^63
        have hw : |(3736250257/10000000000 : ℝ)|=(3736250257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-311766709/625000000 : ℝ)|^79 ≤ (41805992599979/100000000000000 : ℝ)^63
        have hw : |(-311766709/625000000 : ℝ)|=(311766709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3736250317/10000000000 : ℝ)|^79 ≤ (29097003978939/100000000000000 : ℝ)^63
        have hw : |(3736250317/10000000000 : ℝ)|=(3736250317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318070_s0_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (999288647/2000000000 : ℝ)*x 0 + (-2344001709/10000000000 : ℝ)*x 1 + (-4996443411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999288647/2000000000 : ℝ)^79 ≤ (1309122927433/3125000000000 : ℝ)^63 := by
    have hnat : (999288647 : ℕ)^79*3125000000000^63 ≤ 1309122927433^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999288647 2000000000 1309122927433 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2344001709/10000000000 : ℝ)^79 ≤ (16216130773117/100000000000000 : ℝ)^63 := by
    have hnat : (2344001709 : ℕ)^79*100000000000000^63 ≤ 16216130773117^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344001709 10000000000 16216130773117 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4996443411/10000000000 : ℝ)^79 ≤ (41891935528269/100000000000000 : ℝ)^63 := by
    have hnat : (4996443411 : ℕ)^79*100000000000000^63 ≤ 41891935528269^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996443411 10000000000 41891935528269 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(999288647/2000000000 : ℝ), (-2344001709/10000000000 : ℝ), (-4996443411/10000000000 : ℝ)] ![(1309122927433/3125000000000 : ℝ), (16216130773117/100000000000000 : ℝ), (41891935528269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(999288647/2000000000 : ℝ)|^79 ≤ (1309122927433/3125000000000 : ℝ)^63
        have hw : |(999288647/2000000000 : ℝ)|=(999288647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2344001709/10000000000 : ℝ)|^79 ≤ (16216130773117/100000000000000 : ℝ)^63
        have hw : |(-2344001709/10000000000 : ℝ)|=(2344001709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4996443411/10000000000 : ℝ)|^79 ≤ (41891935528269/100000000000000 : ℝ)^63
        have hw : |(-4996443411/10000000000 : ℝ)|=(4996443411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318070 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-267940137/1250000000 : ℝ)*X 0 0+(-800052481/2000000000 : ℝ)*X 0 1+(-610020703/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1525051729/2500000000 : ℝ)*X 1 0+(500032809/1250000000 : ℝ)*X 1 1+(-1071760583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3736250257/10000000000 : ℝ)*X 2 0+(-311766709/625000000 : ℝ)*X 2 1+(3736250317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((999288647/2000000000 : ℝ)*X 0 0+(-2344001709/10000000000 : ℝ)*X 0 1+(-4996443411/10000000000 : ℝ)*X 0 2+(999288647/2000000000 : ℝ)*X 1 0+(-2344001709/10000000000 : ℝ)*X 1 1+(-4996443411/10000000000 : ℝ)*X 1 2+(999288647/2000000000 : ℝ)*X 2 0+(-2344001709/10000000000 : ℝ)*X 2 1+(-4996443411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-1971949956098217763552125459/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4607/50000000000 : ℝ)*(base3) + (12017/500000000000 : ℝ)*(base21) + (115815559967/200000000000 : ℝ)*(base39) + (24603/1000000000000 : ℝ)*(base40) + (53739/1000000000000 : ℝ)*(base43) + (5009590047/31250000000 : ℝ)*(base49) + (178067583871/500000000000 : ℝ)*(base59) + (6641/200000000000 : ℝ)*(base60) + (7299/4000 : ℝ)*(major_s0_0) + (1824749946261/1000000000000 : ℝ)*(major_s0_1) + (7299/4000 : ℝ)*(major_s0_2) + (164329159649/62500000000 : ℝ)*(sp_s0_0) + (2629266700263/1000000000000 : ℝ)*(sp_s0_1) + (52585330607/20000000000 : ℝ)*(sp_s0_2) + (49999995393/50000000000 : ℝ)*(sp_s0_6) + (657316652031/250000000000 : ℝ)*(f.sum) + (165264606370529/5000000000000000000000000000 : ℝ)*base63 + (334912231/250000000000000000000 : ℝ)*base64 + (2499079685881001/5000000000000000000000000000 : ℝ)*base66 + (1612383373/2500000000000000000000 : ℝ)*base69 + (982393349/2500000000000000000000 : ℝ)*base70 + (1429889191/5000000000000000000000 : ℝ)*base72 + (1143982449370529/5000000000000000000000000000 : ℝ)*base75 + (27576217/125000000000000000000 : ℝ)*base76 + (1556027670881001/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c318071_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (897031189/2500000000 : ℝ)*x 0 + (255278419/500000000 : ℝ)*x 1 + (187849933/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897031189/2500000000 : ℝ)^79 ≤ (27657824700693/100000000000000 : ℝ)^63 := by
    have hnat : (897031189 : ℕ)^79*100000000000000^63 ≤ 27657824700693^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897031189 2500000000 27657824700693 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255278419/500000000 : ℝ)^79 ≤ (4304240863667/10000000000000 : ℝ)^63 := by
    have hnat : (255278419 : ℕ)^79*10000000000000^63 ≤ 4304240863667^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255278419 500000000 4304240863667 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187849933/500000000 : ℝ)^79 ≤ (7324941661291/25000000000000 : ℝ)^63 := by
    have hnat : (187849933 : ℕ)^79*25000000000000^63 ≤ 7324941661291^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187849933 500000000 7324941661291 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897031189/2500000000 : ℝ), (255278419/500000000 : ℝ), (187849933/500000000 : ℝ)] ![(27657824700693/100000000000000 : ℝ), (4304240863667/10000000000000 : ℝ), (7324941661291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897031189/2500000000 : ℝ)|^79 ≤ (27657824700693/100000000000000 : ℝ)^63
        have hw : |(897031189/2500000000 : ℝ)|=(897031189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(255278419/500000000 : ℝ)|^79 ≤ (4304240863667/10000000000000 : ℝ)^63
        have hw : |(255278419/500000000 : ℝ)|=(255278419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187849933/500000000 : ℝ)|^79 ≤ (7324941661291/25000000000000 : ℝ)^63
        have hw : |(187849933/500000000 : ℝ)|=(187849933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3177473453/5000000000 : ℝ)*x 0 + (-3642135647/10000000000 : ℝ)*x 1 + (-277986509/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3177473453/5000000000 : ℝ)^79 ≤ (14159522726931/25000000000000 : ℝ)^63 := by
    have hnat : (3177473453 : ℕ)^79*25000000000000^63 ≤ 14159522726931^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177473453 5000000000 14159522726931 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3642135647/10000000000 : ℝ)^79 ≤ (28180876412439/100000000000000 : ℝ)^63 := by
    have hnat : (3642135647 : ℕ)^79*100000000000000^63 ≤ 28180876412439^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642135647 10000000000 28180876412439 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277986509/1250000000 : ℝ)^79 ≤ (7590516330931/50000000000000 : ℝ)^63 := by
    have hnat : (277986509 : ℕ)^79*50000000000000^63 ≤ 7590516330931^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277986509 1250000000 7590516330931 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3177473453/5000000000 : ℝ), (-3642135647/10000000000 : ℝ), (-277986509/1250000000 : ℝ)] ![(14159522726931/25000000000000 : ℝ), (28180876412439/100000000000000 : ℝ), (7590516330931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3177473453/5000000000 : ℝ)|^79 ≤ (14159522726931/25000000000000 : ℝ)^63
        have hw : |(3177473453/5000000000 : ℝ)|=(3177473453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3642135647/10000000000 : ℝ)|^79 ≤ (28180876412439/100000000000000 : ℝ)^63
        have hw : |(-3642135647/10000000000 : ℝ)|=(3642135647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277986509/1250000000 : ℝ)|^79 ≤ (7590516330931/50000000000000 : ℝ)^63
        have hw : |(-277986509/1250000000 : ℝ)|=(277986509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-376954529/1000000000 : ℝ)*x 0 + (-5176945361/10000000000 : ℝ)*x 1 + (1748462659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376954529/1000000000 : ℝ)^79 ≤ (14711258214031/50000000000000 : ℝ)^63 := by
    have hnat : (376954529 : ℕ)^79*50000000000000^63 ≤ 14711258214031^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376954529 1000000000 14711258214031 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176945361/10000000000 : ℝ)^79 ≤ (21899154741149/50000000000000 : ℝ)^63 := by
    have hnat : (5176945361 : ℕ)^79*50000000000000^63 ≤ 21899154741149^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176945361 10000000000 21899154741149 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748462659/5000000000 : ℝ)^79 ≤ (26779174074611/100000000000000 : ℝ)^63 := by
    have hnat : (1748462659 : ℕ)^79*100000000000000^63 ≤ 26779174074611^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748462659 5000000000 26779174074611 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-376954529/1000000000 : ℝ), (-5176945361/10000000000 : ℝ), (1748462659/5000000000 : ℝ)] ![(14711258214031/50000000000000 : ℝ), (21899154741149/50000000000000 : ℝ), (26779174074611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-376954529/1000000000 : ℝ)|^79 ≤ (14711258214031/50000000000000 : ℝ)^63
        have hw : |(-376954529/1000000000 : ℝ)|=(376954529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5176945361/10000000000 : ℝ)|^79 ≤ (21899154741149/50000000000000 : ℝ)^63
        have hw : |(-5176945361/10000000000 : ℝ)|=(5176945361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1748462659/5000000000 : ℝ)|^79 ≤ (26779174074611/100000000000000 : ℝ)^63
        have hw : |(1748462659/5000000000 : ℝ)|=(1748462659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (634868249/2000000000 : ℝ)*x 0 + (5961783993/10000000000 : ℝ)*x 1 + (801142039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (634868249/2000000000 : ℝ)^79 ≤ (5929655447439/25000000000000 : ℝ)^63 := by
    have hnat : (634868249 : ℕ)^79*25000000000000^63 ≤ 5929655447439^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634868249 2000000000 5929655447439 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5961783993/10000000000 : ℝ)^79 ≤ (52279199817487/100000000000000 : ℝ)^63 := by
    have hnat : (5961783993 : ℕ)^79*100000000000000^63 ≤ 52279199817487^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5961783993 10000000000 52279199817487 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801142039/2500000000 : ℝ)^79 ≤ (2400217837099/10000000000000 : ℝ)^63 := by
    have hnat : (801142039 : ℕ)^79*10000000000000^63 ≤ 2400217837099^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801142039 2500000000 2400217837099 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(634868249/2000000000 : ℝ), (5961783993/10000000000 : ℝ), (801142039/2500000000 : ℝ)] ![(5929655447439/25000000000000 : ℝ), (52279199817487/100000000000000 : ℝ), (2400217837099/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(634868249/2000000000 : ℝ)|^79 ≤ (5929655447439/25000000000000 : ℝ)^63
        have hw : |(634868249/2000000000 : ℝ)|=(634868249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5961783993/10000000000 : ℝ)|^79 ≤ (52279199817487/100000000000000 : ℝ)^63
        have hw : |(5961783993/10000000000 : ℝ)|=(5961783993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801142039/2500000000 : ℝ)|^79 ≤ (2400217837099/10000000000000 : ℝ)^63
        have hw : |(801142039/2500000000 : ℝ)|=(801142039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3293006801/5000000000 : ℝ)*x 0 + (-1851538543/5000000000 : ℝ)*x 1 + (-460735337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3293006801/5000000000 : ℝ)^79 ≤ (11846458116739/20000000000000 : ℝ)^63 := by
    have hnat : (3293006801 : ℕ)^79*20000000000000^63 ≤ 11846458116739^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3293006801 5000000000 11846458116739 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1851538543/5000000000 : ℝ)^79 ≤ (575468271849/2000000000000 : ℝ)^63 := by
    have hnat : (1851538543 : ℕ)^79*2000000000000^63 ≤ 575468271849^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851538543 5000000000 575468271849 2000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460735337/2500000000 : ℝ)^79 ≤ (239885916261/2000000000000 : ℝ)^63 := by
    have hnat : (460735337 : ℕ)^79*2000000000000^63 ≤ 239885916261^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460735337 2500000000 239885916261 2000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3293006801/5000000000 : ℝ), (-1851538543/5000000000 : ℝ), (-460735337/2500000000 : ℝ)] ![(11846458116739/20000000000000 : ℝ), (575468271849/2000000000000 : ℝ), (239885916261/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3293006801/5000000000 : ℝ)|^79 ≤ (11846458116739/20000000000000 : ℝ)^63
        have hw : |(3293006801/5000000000 : ℝ)|=(3293006801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1851538543/5000000000 : ℝ)|^79 ≤ (575468271849/2000000000000 : ℝ)^63
        have hw : |(-1851538543/5000000000 : ℝ)|=(1851538543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460735337/2500000000 : ℝ)|^79 ≤ (239885916261/2000000000000 : ℝ)^63
        have hw : |(-460735337/2500000000 : ℝ)|=(460735337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2444951/2000000000 : ℝ)*x 0 + (-1031121/8000000 : ℝ)*x 1 + (9382423599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2444951/2000000000 : ℝ)^79 ≤ (22258281689/100000000000000 : ℝ)^63 := by
    have hnat : (2444951 : ℕ)^79*100000000000000^63 ≤ 22258281689^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2444951 2000000000 22258281689 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031121/8000000 : ℝ)^79 ≤ (3830131510041/50000000000000 : ℝ)^63 := by
    have hnat : (1031121 : ℕ)^79*50000000000000^63 ≤ 3830131510041^63*8000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031121 8000000 3830131510041 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9382423599/10000000000 : ℝ)^79 ≤ (92317478692059/100000000000000 : ℝ)^63 := by
    have hnat : (9382423599 : ℕ)^79*100000000000000^63 ≤ 92317478692059^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9382423599 10000000000 92317478692059 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2444951/2000000000 : ℝ), (-1031121/8000000 : ℝ), (9382423599/10000000000 : ℝ)] ![(22258281689/100000000000000 : ℝ), (3830131510041/50000000000000 : ℝ), (92317478692059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2444951/2000000000 : ℝ)|^79 ≤ (22258281689/100000000000000 : ℝ)^63
        have hw : |(-2444951/2000000000 : ℝ)|=(2444951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031121/8000000 : ℝ)|^79 ≤ (3830131510041/50000000000000 : ℝ)^63
        have hw : |(-1031121/8000000 : ℝ)|=(1031121/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9382423599/10000000000 : ℝ)|^79 ≤ (92317478692059/100000000000000 : ℝ)^63
        have hw : |(9382423599/10000000000 : ℝ)|=(9382423599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1649466309/5000000000 : ℝ)*x 0 + (-590489239/2000000000 : ℝ)*x 1 + (606801027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1649466309/5000000000 : ℝ)^79 ≤ (12445879563993/50000000000000 : ℝ)^63 := by
    have hnat : (1649466309 : ℕ)^79*50000000000000^63 ≤ 12445879563993^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649466309 5000000000 12445879563993 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590489239/2000000000 : ℝ)^79 ≤ (4331666705783/20000000000000 : ℝ)^63 := by
    have hnat : (590489239 : ℕ)^79*20000000000000^63 ≤ 4331666705783^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590489239 2000000000 4331666705783 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606801027/1000000000 : ℝ)^79 ≤ (1336247683277/2500000000000 : ℝ)^63 := by
    have hnat : (606801027 : ℕ)^79*2500000000000^63 ≤ 1336247683277^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606801027 1000000000 1336247683277 2500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1649466309/5000000000 : ℝ), (-590489239/2000000000 : ℝ), (606801027/1000000000 : ℝ)] ![(12445879563993/50000000000000 : ℝ), (4331666705783/20000000000000 : ℝ), (1336247683277/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1649466309/5000000000 : ℝ)|^79 ≤ (12445879563993/50000000000000 : ℝ)^63
        have hw : |(-1649466309/5000000000 : ℝ)|=(1649466309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-590489239/2000000000 : ℝ)|^79 ≤ (4331666705783/20000000000000 : ℝ)^63
        have hw : |(-590489239/2000000000 : ℝ)|=(590489239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606801027/1000000000 : ℝ)|^79 ≤ (1336247683277/2500000000000 : ℝ)^63
        have hw : |(606801027/1000000000 : ℝ)|=(606801027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5565488613/10000000000 : ℝ)*x 0 + (4385441351/10000000000 : ℝ)*x 1 + (148326957/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5565488613/10000000000 : ℝ)^79 ≤ (2997431265013/6250000000000 : ℝ)^63 := by
    have hnat : (5565488613 : ℕ)^79*6250000000000^63 ≤ 2997431265013^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565488613 10000000000 2997431265013 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4385441351/10000000000 : ℝ)^79 ≤ (7114199630529/20000000000000 : ℝ)^63 := by
    have hnat : (4385441351 : ℕ)^79*20000000000000^63 ≤ 7114199630529^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385441351 10000000000 7114199630529 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148326957/625000000 : ℝ)^79 ≤ (4117525396731/25000000000000 : ℝ)^63 := by
    have hnat : (148326957 : ℕ)^79*25000000000000^63 ≤ 4117525396731^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148326957 625000000 4117525396731 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5565488613/10000000000 : ℝ), (4385441351/10000000000 : ℝ), (148326957/625000000 : ℝ)] ![(2997431265013/6250000000000 : ℝ), (7114199630529/20000000000000 : ℝ), (4117525396731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5565488613/10000000000 : ℝ)|^79 ≤ (2997431265013/6250000000000 : ℝ)^63
        have hw : |(5565488613/10000000000 : ℝ)|=(5565488613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4385441351/10000000000 : ℝ)|^79 ≤ (7114199630529/20000000000000 : ℝ)^63
        have hw : |(4385441351/10000000000 : ℝ)|=(4385441351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148326957/625000000 : ℝ)|^79 ≤ (4117525396731/25000000000000 : ℝ)^63
        have hw : |(148326957/625000000 : ℝ)|=(148326957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7955140749/10000000000 : ℝ)*x 0 + (-1317873181/5000000000 : ℝ)*x 1 + (-1082255849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7955140749/10000000000 : ℝ)^79 ≤ (18765303338671/25000000000000 : ℝ)^63 := by
    have hnat : (7955140749 : ℕ)^79*25000000000000^63 ≤ 18765303338671^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7955140749 10000000000 18765303338671 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317873181/5000000000 : ℝ)^79 ≤ (3757175777957/20000000000000 : ℝ)^63 := by
    have hnat : (1317873181 : ℕ)^79*20000000000000^63 ≤ 3757175777957^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317873181 5000000000 3757175777957 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082255849/10000000000 : ℝ)^79 ≤ (6152907738379/100000000000000 : ℝ)^63 := by
    have hnat : (1082255849 : ℕ)^79*100000000000000^63 ≤ 6152907738379^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082255849 10000000000 6152907738379 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7955140749/10000000000 : ℝ), (-1317873181/5000000000 : ℝ), (-1082255849/10000000000 : ℝ)] ![(18765303338671/25000000000000 : ℝ), (3757175777957/20000000000000 : ℝ), (6152907738379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7955140749/10000000000 : ℝ)|^79 ≤ (18765303338671/25000000000000 : ℝ)^63
        have hw : |(7955140749/10000000000 : ℝ)|=(7955140749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1317873181/5000000000 : ℝ)|^79 ≤ (3757175777957/20000000000000 : ℝ)^63
        have hw : |(-1317873181/5000000000 : ℝ)|=(1317873181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082255849/10000000000 : ℝ)|^79 ≤ (6152907738379/100000000000000 : ℝ)^63
        have hw : |(-1082255849/10000000000 : ℝ)|=(1082255849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-239533/5000000000 : ℝ)*x 0 + (-1697095471/10000000000 : ℝ)*x 1 + (9127524603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239533/5000000000 : ℝ)^79 ≤ (191567973/50000000000000 : ℝ)^63 := by
    have hnat : (239533 : ℕ)^79*50000000000000^63 ≤ 191567973^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239533 5000000000 191567973 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1697095471/10000000000 : ℝ)^79 ≤ (10816235187093/100000000000000 : ℝ)^63 := by
    have hnat : (1697095471 : ℕ)^79*100000000000000^63 ≤ 10816235187093^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697095471 10000000000 10816235187093 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9127524603/10000000000 : ℝ)^79 ≤ (17836676335007/20000000000000 : ℝ)^63 := by
    have hnat : (9127524603 : ℕ)^79*20000000000000^63 ≤ 17836676335007^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9127524603 10000000000 17836676335007 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239533/5000000000 : ℝ), (-1697095471/10000000000 : ℝ), (9127524603/10000000000 : ℝ)] ![(191567973/50000000000000 : ℝ), (10816235187093/100000000000000 : ℝ), (17836676335007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239533/5000000000 : ℝ)|^79 ≤ (191567973/50000000000000 : ℝ)^63
        have hw : |(-239533/5000000000 : ℝ)|=(239533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1697095471/10000000000 : ℝ)|^79 ≤ (10816235187093/100000000000000 : ℝ)^63
        have hw : |(-1697095471/10000000000 : ℝ)|=(1697095471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9127524603/10000000000 : ℝ)|^79 ≤ (17836676335007/20000000000000 : ℝ)^63
        have hw : |(9127524603/10000000000 : ℝ)|=(9127524603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-681135219/2000000000 : ℝ)*x 0 + (-2176841477/5000000000 : ℝ)*x 1 + (4704522459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681135219/2000000000 : ℝ)^79 ≤ (1295292481269/5000000000000 : ℝ)^63 := by
    have hnat : (681135219 : ℕ)^79*5000000000000^63 ≤ 1295292481269^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681135219 2000000000 1295292481269 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176841477/5000000000 : ℝ)^79 ≤ (70496553779/200000000000 : ℝ)^63 := by
    have hnat : (2176841477 : ℕ)^79*200000000000^63 ≤ 70496553779^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176841477 5000000000 70496553779 200000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4704522459/10000000000 : ℝ)^79 ≤ (2427867091767/6250000000000 : ℝ)^63 := by
    have hnat : (4704522459 : ℕ)^79*6250000000000^63 ≤ 2427867091767^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704522459 10000000000 2427867091767 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-681135219/2000000000 : ℝ), (-2176841477/5000000000 : ℝ), (4704522459/10000000000 : ℝ)] ![(1295292481269/5000000000000 : ℝ), (70496553779/200000000000 : ℝ), (2427867091767/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-681135219/2000000000 : ℝ)|^79 ≤ (1295292481269/5000000000000 : ℝ)^63
        have hw : |(-681135219/2000000000 : ℝ)|=(681135219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176841477/5000000000 : ℝ)|^79 ≤ (70496553779/200000000000 : ℝ)^63
        have hw : |(-2176841477/5000000000 : ℝ)|=(2176841477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4704522459/10000000000 : ℝ)|^79 ≤ (2427867091767/6250000000000 : ℝ)^63
        have hw : |(4704522459/10000000000 : ℝ)|=(4704522459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (183689431/625000000 : ℝ)*x 0 + (560908581/1000000000 : ℝ)*x 1 + (119748261/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183689431/625000000 : ℝ)^79 ≤ (10767500305779/50000000000000 : ℝ)^63 := by
    have hnat : (183689431 : ℕ)^79*50000000000000^63 ≤ 10767500305779^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183689431 625000000 10767500305779 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560908581/1000000000 : ℝ)^79 ≤ (48430465691621/100000000000000 : ℝ)^63 := by
    have hnat : (560908581 : ℕ)^79*100000000000000^63 ≤ 48430465691621^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560908581 1000000000 48430465691621 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119748261/312500000 : ℝ)^79 ≤ (15017266843491/50000000000000 : ℝ)^63 := by
    have hnat : (119748261 : ℕ)^79*50000000000000^63 ≤ 15017266843491^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119748261 312500000 15017266843491 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(183689431/625000000 : ℝ), (560908581/1000000000 : ℝ), (119748261/312500000 : ℝ)] ![(10767500305779/50000000000000 : ℝ), (48430465691621/100000000000000 : ℝ), (15017266843491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(183689431/625000000 : ℝ)|^79 ≤ (10767500305779/50000000000000 : ℝ)^63
        have hw : |(183689431/625000000 : ℝ)|=(183689431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560908581/1000000000 : ℝ)|^79 ≤ (48430465691621/100000000000000 : ℝ)^63
        have hw : |(560908581/1000000000 : ℝ)|=(560908581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119748261/312500000 : ℝ)|^79 ≤ (15017266843491/50000000000000 : ℝ)^63
        have hw : |(119748261/312500000 : ℝ)|=(119748261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7227923029/10000000000 : ℝ)*x 0 + (-182312681/625000000 : ℝ)*x 1 + (-1856873221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7227923029/10000000000 : ℝ)^79 ≤ (66559098128979/100000000000000 : ℝ)^63 := by
    have hnat : (7227923029 : ℕ)^79*100000000000000^63 ≤ 66559098128979^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7227923029 10000000000 66559098128979 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182312681/625000000 : ℝ)^79 ≤ (10666398702429/50000000000000 : ℝ)^63 := by
    have hnat : (182312681 : ℕ)^79*50000000000000^63 ≤ 10666398702429^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182312681 625000000 10666398702429 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856873221/10000000000 : ℝ)^79 ≤ (2421620889363/20000000000000 : ℝ)^63 := by
    have hnat : (1856873221 : ℕ)^79*20000000000000^63 ≤ 2421620889363^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856873221 10000000000 2421620889363 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7227923029/10000000000 : ℝ), (-182312681/625000000 : ℝ), (-1856873221/10000000000 : ℝ)] ![(66559098128979/100000000000000 : ℝ), (10666398702429/50000000000000 : ℝ), (2421620889363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7227923029/10000000000 : ℝ)|^79 ≤ (66559098128979/100000000000000 : ℝ)^63
        have hw : |(7227923029/10000000000 : ℝ)|=(7227923029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182312681/625000000 : ℝ)|^79 ≤ (10666398702429/50000000000000 : ℝ)^63
        have hw : |(-182312681/625000000 : ℝ)|=(182312681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1856873221/10000000000 : ℝ)|^79 ≤ (2421620889363/20000000000000 : ℝ)^63
        have hw : |(-1856873221/10000000000 : ℝ)|=(1856873221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-691685407/2000000000 : ℝ)*x 0 + (-958356171/2500000000 : ℝ)*x 1 + (2576334363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (691685407/2000000000 : ℝ)^79 ≤ (13205000726247/50000000000000 : ℝ)^63 := by
    have hnat : (691685407 : ℕ)^79*50000000000000^63 ≤ 13205000726247^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691685407 2000000000 13205000726247 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958356171/2500000000 : ℝ)^79 ≤ (6009816775441/20000000000000 : ℝ)^63 := by
    have hnat : (958356171 : ℕ)^79*20000000000000^63 ≤ 6009816775441^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958356171 2500000000 6009816775441 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576334363/5000000000 : ℝ)^79 ≤ (21770457330181/50000000000000 : ℝ)^63 := by
    have hnat : (2576334363 : ℕ)^79*50000000000000^63 ≤ 21770457330181^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576334363 5000000000 21770457330181 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-691685407/2000000000 : ℝ), (-958356171/2500000000 : ℝ), (2576334363/5000000000 : ℝ)] ![(13205000726247/50000000000000 : ℝ), (6009816775441/20000000000000 : ℝ), (21770457330181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-691685407/2000000000 : ℝ)|^79 ≤ (13205000726247/50000000000000 : ℝ)^63
        have hw : |(-691685407/2000000000 : ℝ)|=(691685407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-958356171/2500000000 : ℝ)|^79 ≤ (6009816775441/20000000000000 : ℝ)^63
        have hw : |(-958356171/2500000000 : ℝ)|=(958356171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576334363/5000000000 : ℝ)|^79 ≤ (21770457330181/50000000000000 : ℝ)^63
        have hw : |(2576334363/5000000000 : ℝ)|=(2576334363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8453157/20000000 : ℝ)*x 0 + (2349708593/5000000000 : ℝ)*x 1 + (886319217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8453157/20000000 : ℝ)^79 ≤ (4245335492201/12500000000000 : ℝ)^63 := by
    have hnat : (8453157 : ℕ)^79*12500000000000^63 ≤ 4245335492201^63*20000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8453157 20000000 4245335492201 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2349708593/5000000000 : ℝ)^79 ≤ (38793019817489/100000000000000 : ℝ)^63 := by
    have hnat : (2349708593 : ℕ)^79*100000000000000^63 ≤ 38793019817489^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349708593 5000000000 38793019817489 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886319217/2500000000 : ℝ)^79 ≤ (13622148113817/50000000000000 : ℝ)^63 := by
    have hnat : (886319217 : ℕ)^79*50000000000000^63 ≤ 13622148113817^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886319217 2500000000 13622148113817 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8453157/20000000 : ℝ), (2349708593/5000000000 : ℝ), (886319217/2500000000 : ℝ)] ![(4245335492201/12500000000000 : ℝ), (38793019817489/100000000000000 : ℝ), (13622148113817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8453157/20000000 : ℝ)|^79 ≤ (4245335492201/12500000000000 : ℝ)^63
        have hw : |(8453157/20000000 : ℝ)|=(8453157/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2349708593/5000000000 : ℝ)|^79 ≤ (38793019817489/100000000000000 : ℝ)^63
        have hw : |(2349708593/5000000000 : ℝ)|=(2349708593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886319217/2500000000 : ℝ)|^79 ≤ (13622148113817/50000000000000 : ℝ)^63
        have hw : |(886319217/2500000000 : ℝ)|=(886319217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5119127363/10000000000 : ℝ)*x 0 + (-104815297/250000000 : ℝ)*x 1 + (-3118161453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5119127363/10000000000 : ℝ)^79 ≤ (8637159304749/20000000000000 : ℝ)^63 := by
    have hnat : (5119127363 : ℕ)^79*20000000000000^63 ≤ 8637159304749^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119127363 10000000000 8637159304749 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104815297/250000000 : ℝ)^79 ≤ (4202597153347/12500000000000 : ℝ)^63 := by
    have hnat : (104815297 : ℕ)^79*12500000000000^63 ≤ 4202597153347^63*250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104815297 250000000 4202597153347 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118161453/10000000000 : ℝ)^79 ≤ (5798356557409/25000000000000 : ℝ)^63 := by
    have hnat : (3118161453 : ℕ)^79*25000000000000^63 ≤ 5798356557409^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118161453 10000000000 5798356557409 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5119127363/10000000000 : ℝ), (-104815297/250000000 : ℝ), (-3118161453/10000000000 : ℝ)] ![(8637159304749/20000000000000 : ℝ), (4202597153347/12500000000000 : ℝ), (5798356557409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5119127363/10000000000 : ℝ)|^79 ≤ (8637159304749/20000000000000 : ℝ)^63
        have hw : |(5119127363/10000000000 : ℝ)|=(5119127363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104815297/250000000 : ℝ)|^79 ≤ (4202597153347/12500000000000 : ℝ)^63
        have hw : |(-104815297/250000000 : ℝ)|=(104815297/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3118161453/10000000000 : ℝ)|^79 ≤ (5798356557409/25000000000000 : ℝ)^63
        have hw : |(-3118161453/10000000000 : ℝ)|=(3118161453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s1_5 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-117/2000000000 : ℝ)*x 0 + (-117/2000000000 : ℝ)*x 1 + (4999999993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117/2000000000 : ℝ)^79 ≤ (42581/50000000000000 : ℝ)^63 := by
    have hnat : (117 : ℕ)^79*50000000000000^63 ≤ 42581^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117 2000000000 42581 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117/2000000000 : ℝ)^79 ≤ (42581/50000000000000 : ℝ)^63 := by
    have hnat : (117 : ℕ)^79*50000000000000^63 ≤ 42581^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117 2000000000 42581 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999999993/5000000000 : ℝ)^79 ≤ (19999999964889/20000000000000 : ℝ)^63 := by
    have hnat : (4999999993 : ℕ)^79*20000000000000^63 ≤ 19999999964889^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999993 5000000000 19999999964889 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117/2000000000 : ℝ), (-117/2000000000 : ℝ), (4999999993/5000000000 : ℝ)] ![(42581/50000000000000 : ℝ), (42581/50000000000000 : ℝ), (19999999964889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117/2000000000 : ℝ)|^79 ≤ (42581/50000000000000 : ℝ)^63
        have hw : |(-117/2000000000 : ℝ)|=(117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117/2000000000 : ℝ)|^79 ≤ (42581/50000000000000 : ℝ)^63
        have hw : |(-117/2000000000 : ℝ)|=(117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999999993/5000000000 : ℝ)|^79 ≤ (19999999964889/20000000000000 : ℝ)^63
        have hw : |(4999999993/5000000000 : ℝ)|=(4999999993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318071_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (153610777/500000000 : ℝ)*x 0 + (-639263839/2000000000 : ℝ)*x 1 + (3027651659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153610777/500000000 : ℝ)^79 ≤ (22765682782577/100000000000000 : ℝ)^63 := by
    have hnat : (153610777 : ℕ)^79*100000000000000^63 ≤ 22765682782577^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153610777 500000000 22765682782577 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639263839/2000000000 : ℝ)^79 ≤ (23924727757021/100000000000000 : ℝ)^63 := by
    have hnat : (639263839 : ℕ)^79*100000000000000^63 ≤ 23924727757021^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639263839 2000000000 23924727757021 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3027651659/5000000000 : ℝ)^79 ≤ (26654794724777/50000000000000 : ℝ)^63 := by
    have hnat : (3027651659 : ℕ)^79*50000000000000^63 ≤ 26654794724777^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3027651659 5000000000 26654794724777 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(153610777/500000000 : ℝ), (-639263839/2000000000 : ℝ), (3027651659/5000000000 : ℝ)] ![(22765682782577/100000000000000 : ℝ), (23924727757021/100000000000000 : ℝ), (26654794724777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(153610777/500000000 : ℝ)|^79 ≤ (22765682782577/100000000000000 : ℝ)^63
        have hw : |(153610777/500000000 : ℝ)|=(153610777/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639263839/2000000000 : ℝ)|^79 ≤ (23924727757021/100000000000000 : ℝ)^63
        have hw : |(-639263839/2000000000 : ℝ)|=(639263839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3027651659/5000000000 : ℝ)|^79 ≤ (26654794724777/50000000000000 : ℝ)^63
        have hw : |(3027651659/5000000000 : ℝ)|=(3027651659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318071 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((897031189/2500000000 : ℝ)*X 1 0+(255278419/500000000 : ℝ)*X 1 1+(187849933/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3177473453/5000000000 : ℝ)*X 2 0+(-3642135647/10000000000 : ℝ)*X 2 1+(-277986509/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-376954529/1000000000 : ℝ)*X 0 0+(-5176945361/10000000000 : ℝ)*X 0 1+(1748462659/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((634868249/2000000000 : ℝ)*X 1 0+(5961783993/10000000000 : ℝ)*X 1 1+(801142039/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3293006801/5000000000 : ℝ)*X 2 0+(-1851538543/5000000000 : ℝ)*X 2 1+(-460735337/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2444951/2000000000 : ℝ)*X 0 0+(-1031121/8000000 : ℝ)*X 0 1+(9382423599/10000000000 : ℝ)*X 0 2+(-2444951/2000000000 : ℝ)*X 1 0+(-1031121/8000000 : ℝ)*X 1 1+(9382423599/10000000000 : ℝ)*X 1 2+(-2444951/2000000000 : ℝ)*X 2 0+(-1031121/8000000 : ℝ)*X 2 1+(9382423599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1649466309/5000000000 : ℝ)*X 0 0+(-590489239/2000000000 : ℝ)*X 0 1+(606801027/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((5565488613/10000000000 : ℝ)*X 1 0+(4385441351/10000000000 : ℝ)*X 1 1+(148326957/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7955140749/10000000000 : ℝ)*X 2 0+(-1317873181/5000000000 : ℝ)*X 2 1+(-1082255849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-239533/5000000000 : ℝ)*X 0 0+(-1697095471/10000000000 : ℝ)*X 0 1+(9127524603/10000000000 : ℝ)*X 0 2+(-239533/5000000000 : ℝ)*X 1 0+(-1697095471/10000000000 : ℝ)*X 1 1+(9127524603/10000000000 : ℝ)*X 1 2+(-239533/5000000000 : ℝ)*X 2 0+(-1697095471/10000000000 : ℝ)*X 2 1+(9127524603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-681135219/2000000000 : ℝ)*X 0 0+(-2176841477/5000000000 : ℝ)*X 0 1+(4704522459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((183689431/625000000 : ℝ)*X 1 0+(560908581/1000000000 : ℝ)*X 1 1+(119748261/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((7227923029/10000000000 : ℝ)*X 2 0+(-182312681/625000000 : ℝ)*X 2 1+(-1856873221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((42059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7873099704650002933407/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53310102367/500000000000 : ℝ)*(base1) + (52501654889/100000000000 : ℝ)*(base7) + (285682877761/500000000000 : ℝ)*(base54) + (827011627053/1000000000000 : ℝ)*(base60) + (2752910722049/1000000000000 : ℝ)*(major_s0_0) + (2752910722049/1000000000000 : ℝ)*(major_s0_1) + (2181544966527/1000000000000 : ℝ)*(major_s0_2) + (150915401/500000000000 : ℝ)*(sp_s0_2) + (475490681459/125000000000 : ℝ)*(sp_s0_7) + (3697295611609/1000000000000 : ℝ)*(sp_s0_8) + (1562818830307/500000000000 : ℝ)*(sp_s0_9) + (1355553330801/1000000000000 : ℝ)*(sp_s0_13) + (128153599/1000000000000 : ℝ)*(sp_s0_20) + (9635329/1000000000000 : ℝ)*(sp_s0_22) + (754325447883/500000000000 : ℝ)*(f.failure) + (1848652623469/500000000000 : ℝ)*(f.sum) + (1270932233437823/2500000000000000000000000000 : ℝ)*base62 + (692316886904003/5000000000000000000000000000 : ℝ)*base65 + (355689889727291/5000000000000000000000000000 : ℝ)*base66 + (1021700897227707/5000000000000000000000000000 : ℝ)*base68 + (326694054209589/625000000000000000000000000 : ℝ)*base71 + (776906899852061/5000000000000000000000000000 : ℝ)*base72 + (1007488520352061/5000000000000000000000000000 : ℝ)*base75 + (457569005227291/5000000000000000000000000000 : ℝ)*base76 + (200005541197419/625000000000000000000000000 : ℝ)*base78 + (17/2000000000000000 : ℝ)*base87 + (17/2000000000000000 : ℝ)*base89 + (17/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-70837/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-70837/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7832984153524974850011/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40298325877/62500000000 : ℝ)*(base1) + (615073684601/500000000000 : ℝ)*(base7) + (191740494199/1000000000000 : ℝ)*(base40) + (3725427567/7812500000 : ℝ)*(base60) + (547946822033/250000000000 : ℝ)*(major_s0_0) + (547946822033/250000000000 : ℝ)*(major_s0_1) + (547946822033/250000000000 : ℝ)*(major_s0_2) + (18642291/500000000000 : ℝ)*(sp_s0_1) + (31149039/100000000000 : ℝ)*(sp_s0_13) + (3124601066559/1000000000000 : ℝ)*(sp_s0_14) + (1239895283973/500000000000 : ℝ)*(sp_s0_15) + (1239912107163/500000000000 : ℝ)*(sp_s0_16) + (1786206541/1000000000 : ℝ)*(sp_s0_20) + (3638201/1000000000000 : ℝ)*(sp_s0_23) + (60057193811/50000000000 : ℝ)*(f.failure) + (154989240783/62500000000 : ℝ)*(f.sum) + (44642658885677/156250000000000000000000000 : ℝ)*base62 + (127738243529163/1250000000000000000000000000 : ℝ)*base64 + (202508385931253/1250000000000000000000000000 : ℝ)*base67 + (136920633431253/1250000000000000000000000000 : ℝ)*base68 + (19448581647291/125000000000000000000000000 : ℝ)*base70 + (180459446404163/1250000000000000000000000000 : ℝ)*base73 + (902013999220837/1250000000000000000000000000 : ℝ)*base75 + (695328095568747/1250000000000000000000000000 : ℝ)*base76 + (3662236986849/78125000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (89/200000000000000 : ℝ)*base87 + (89/200000000000000 : ℝ)*base89 + (89/200000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(43443/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(43443/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11513435420524861928709/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1423773647177/500000000000 : ℝ)*(base1) + (1132815353883/1000000000000 : ℝ)*(base7) + (757186590951/500000000000 : ℝ)*(base40) + (10115779509/20000000000 : ℝ)*(base60) + (3128957108373/1000000000000 : ℝ)*(major_s0_0) + (3128957108373/1000000000000 : ℝ)*(major_s0_1) + (3128957108373/1000000000000 : ℝ)*(major_s0_2) + (1705179/250000000000 : ℝ)*(sp_s0_1) + (9039749/1000000000000 : ℝ)*(sp_s0_7) + (10459599/200000000000 : ℝ)*(sp_s0_8) + (81847/50000000000 : ℝ)*(sp_s0_16) + (3371854985627/500000000000 : ℝ)*(sp_s0_21) + (1948056298969/500000000000 : ℝ)*(sp_s0_22) + (3896170079709/1000000000000 : ℝ)*(sp_s0_23) + (171473194047/100000000000 : ℝ)*(f.failure) + (3896171716649/1000000000000 : ℝ)*(f.sum) + (49765829689863/625000000000000000000000000 : ℝ)*base63 + (3786052005732097/5000000000000000000000000000 : ℝ)*base65 + (2963630698286807/5000000000000000000000000000 : ℝ)*base66 + (2503519445213193/5000000000000000000000000000 : ℝ)*base68 + (139606439144529/500000000000000000000000000 : ℝ)*base71 + (3694989631232097/5000000000000000000000000000 : ℝ)*base72 + (2496120657267903/5000000000000000000000000000 : ℝ)*base74 + (3130123457713193/5000000000000000000000000000 : ℝ)*base77 + (229907074127363/625000000000000000000000000 : ℝ)*base78 + (147/400000000000000 : ℝ)*base86 + (147/400000000000000 : ℝ)*base88 + (147/400000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (42059/100000 : ℝ) ^ (39/8 : ℝ) ≤ (733301122302107421/50000000000000000000 : ℝ) := by
    have hpowers : (42059/100000 : ℝ)^39 ≤ (733301122302107421/50000000000000000000 : ℝ)^8 := by
      have hnat : (42059 : ℕ)^39*50000000000000000000^8 ≤ 733301122302107421^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42059 100000 733301122302107421 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42059/100000 : ℝ)) (X := (733301122302107421/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50733301122302107421/50000000000000000000 : ℝ) ≤ (401196412682821/400000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50733301122302107421/50000000000000000000 : ℝ)^8 ≤ (401196412682821/400000000000000 : ℝ)^39 := by
      have hnat : (50733301122302107421 : ℕ)^8*400000000000000^39 ≤ 401196412682821^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50733301122302107421 50000000000000000000 401196412682821 400000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401196412682821/400000000000000 : ℝ)) (X := (50733301122302107421/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25733301122302107421/25000000000000000000 : ℝ) ≤ (10059478941280521/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25733301122302107421/25000000000000000000 : ℝ)^8 ≤ (10059478941280521/10000000000000000 : ℝ)^39 := by
      have hnat : (25733301122302107421 : ℕ)^8*10000000000000000^39 ≤ 10059478941280521^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25733301122302107421 25000000000000000000 10059478941280521 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059478941280521/10000000000000000 : ℝ)) (X := (25733301122302107421/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1196412682821/168236000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7392156052499/1051475000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (42059/100000 : ℝ)) (alpha := (1196412682821/168236000000000 : ℝ)) (beta := (7392156052499/1051475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42059/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1196412682821/168236000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7392156052499/1051475000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (70837/100000 : ℝ) ^ (39/8 : ℝ) ≤ (18621655203072239399/100000000000000000000 : ℝ) := by
    have hpowers : (70837/100000 : ℝ)^39 ≤ (18621655203072239399/100000000000000000000 : ℝ)^8 := by
      have hnat : (70837 : ℕ)^39*100000000000000000000^8 ≤ 18621655203072239399^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70837 100000 18621655203072239399 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70837/100000 : ℝ)) (X := (18621655203072239399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (118621655203072239399/100000000000000000000 : ℝ) ≤ (10356502731293109/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (118621655203072239399/100000000000000000000 : ℝ)^8 ≤ (10356502731293109/10000000000000000 : ℝ)^39 := by
      have hnat : (118621655203072239399 : ℕ)^8*10000000000000000^39 ≤ 10356502731293109^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118621655203072239399 100000000000000000000 10356502731293109 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10356502731293109/10000000000000000 : ℝ)) (X := (118621655203072239399/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (68621655203072239399/50000000000000000000 : ℝ) ≤ (2134191154966127/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (68621655203072239399/50000000000000000000 : ℝ)^8 ≤ (2134191154966127/2000000000000000 : ℝ)^39 := by
      have hnat : (68621655203072239399 : ℕ)^8*2000000000000000^39 ≤ 2134191154966127^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68621655203072239399 50000000000000000000 2134191154966127 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2134191154966127/2000000000000000 : ℝ)) (X := (68621655203072239399/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(356502731293109/7083700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(157226521768763/3541850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (70837/100000 : ℝ)) (alpha := (356502731293109/7083700000000000 : ℝ)) (beta := (157226521768763/3541850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (70837/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(356502731293109/7083700000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(157226521768763/3541850000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (43443/100000 : ℝ) ^ (39/8 : ℝ) ≤ (1717350991875367389/100000000000000000000 : ℝ) := by
    have hpowers : (43443/100000 : ℝ)^39 ≤ (1717350991875367389/100000000000000000000 : ℝ)^8 := by
      have hnat : (43443 : ℕ)^39*100000000000000000000^8 ≤ 1717350991875367389^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43443 100000 1717350991875367389 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43443/100000 : ℝ)) (X := (1717350991875367389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101717350991875367389/100000000000000000000 : ℝ) ≤ (1254373713965509/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (101717350991875367389/100000000000000000000 : ℝ)^8 ≤ (1254373713965509/1250000000000000 : ℝ)^39 := by
      have hnat : (101717350991875367389 : ℕ)^8*1250000000000000^39 ≤ 1254373713965509^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101717350991875367389 100000000000000000000 1254373713965509 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254373713965509/1250000000000000 : ℝ)) (X := (101717350991875367389/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51717350991875367389/50000000000000000000 : ℝ) ≤ (10069512958297001/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (51717350991875367389/50000000000000000000 : ℝ)^8 ≤ (10069512958297001/10000000000000000 : ℝ)^39 := by
      have hnat : (51717350991875367389 : ℕ)^8*10000000000000000^39 ≤ 10069512958297001^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51717350991875367389 50000000000000000000 10069512958297001 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10069512958297001/10000000000000000 : ℝ)) (X := (51717350991875367389/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4373713965509/543037500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3835916285881/482700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (43443/100000 : ℝ)) (alpha := (4373713965509/543037500000000 : ℝ)) (beta := (3835916285881/482700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (43443/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4373713965509/543037500000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3835916285881/482700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-691685407/2000000000 : ℝ)*X 0 0+(-958356171/2500000000 : ℝ)*X 0 1+(2576334363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((8453157/20000000 : ℝ)*X 1 0+(2349708593/5000000000 : ℝ)*X 1 1+(886319217/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5119127363/10000000000 : ℝ)*X 2 0+(-104815297/250000000 : ℝ)*X 2 1+(-3118161453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_5 : ((-117/2000000000 : ℝ)*X 0 0+(-117/2000000000 : ℝ)*X 0 1+(4999999993/5000000000 : ℝ)*X 0 2+(-117/2000000000 : ℝ)*X 1 0+(-117/2000000000 : ℝ)*X 1 1+(4999999993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s1_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((153610777/500000000 : ℝ)*X 0 0+(-639263839/2000000000 : ℝ)*X 0 1+(3027651659/5000000000 : ℝ)*X 0 2+(153610777/500000000 : ℝ)*X 1 0+(-639263839/2000000000 : ℝ)*X 1 1+(3027651659/5000000000 : ℝ)*X 1 2+(153610777/500000000 : ℝ)*X 2 0+(-639263839/2000000000 : ℝ)*X 2 1+(3027651659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-16830148695683691121532504469646870081/2157186335961150000000000000000000000 : ℝ) := by norm_num
    linear_combination (32090138733/100000000000 : ℝ)*(base1) + (104789/1000000000000 : ℝ)*(base10) + (48347/250000000000 : ℝ)*(base17) + (21787/62500000000 : ℝ)*(base21) + (2017469663/4000000000 : ℝ)*(base40) + (101908214931/500000000000 : ℝ)*(base49) + (50224137739/100000000000 : ℝ)*(base60) + (7299/4000 : ℝ)*(major_s1_0) + (7299/4000 : ℝ)*(major_s1_1) + (1824782516101/1000000000000 : ℝ)*(major_s1_2) + (730383523441/250000000000 : ℝ)*(sp_s1_0) + (520126523567/200000000000 : ℝ)*(sp_s1_1) + (2600632462631/1000000000000 : ℝ)*(sp_s1_2) + (32516101/1000000000000 : ℝ)*(sp_s1_5) + (67909861267/100000000000 : ℝ)*(sp_s1_6) + (2600632811223/1000000000000 : ℝ)*(f.sum) + (59460977160375739543/153868589550000000000000000000000 : ℝ)*base63 + (309721545158011/482700000000000000000000000 : ℝ)*base64 + (18626009776547/70837000000000000000000000 : ℝ)*base66 + (314526796857139/2172150000000000000000000000 : ℝ)*base69 + (7653223853510550629/20301879300000000000000000000000 : ℝ)*base70 + (4309412401567/210295000000000000000000000 : ℝ)*base72 + (212200643454961/708370000000000000000000000 : ℝ)*base74 + (14797334038113/42059000000000000000000000 : ℝ)*base76 + (672208932657252111/29793333830000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p018_b031 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c318070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c318071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b031 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
