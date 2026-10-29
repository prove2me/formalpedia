-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_positive87
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:57:52.636482+00:00
-- url     : https://prove2.me/submissions/1763226e-006e-49e2-b5bf-d3c6710d021e

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
namespace HlawkaSchatten.DiagonalCutoff4
theorem positive_chart_nonnegative {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true)) :
    ∀ i h, 0 ≤ pair X i h := by
  intro i h
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hh.1.trans hh.2.1).trans hh.2.2
  · exact hh.1.trans hh.2.1
  · exact hh.1
theorem positive_chart_tailratio {p k A d rho : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    {orders : Fin 3 → Fin 3 → Fin 3}
    (hX : OrderedChart p k A d X orders (fun _ _ => true))
    (hm : ∀ i, orders i 0=i)
    (hbig : ∀ i, pair X i (orders i 1) ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i := by
  intro i h hih
  rw [abs_of_nonneg (positive_chart_nonnegative hX i h)]
  obtain ⟨j,rfl⟩ := (hX.permutation i).2 h
  have hh := hX.ordered i
  simp only [signedPair,signValue,Bool.true_eq,if_true,one_mul] at hh
  fin_cases j
  · exact (hih (hm i).symm).elim
  · exact hbig i
  · exact hh.2.1.trans (hbig i)
end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324087_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-98102887/5000000000 : ℝ)*x 0 + (5495723527/10000000000 : ℝ)*x 1 + (5823879729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98102887/5000000000 : ℝ)^85 ≤ (788531167743/100000000000000 : ℝ)^69 := by
    have hnat : (98102887 : ℕ)^85*100000000000000^69 ≤ 788531167743^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98102887 5000000000 788531167743 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495723527/10000000000 : ℝ)^85 ≤ (2989653160607/6250000000000 : ℝ)^69 := by
    have hnat : (5495723527 : ℕ)^85*6250000000000^69 ≤ 2989653160607^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495723527 10000000000 2989653160607 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5823879729/10000000000 : ℝ)^85 ≤ (5137701824579/10000000000000 : ℝ)^69 := by
    have hnat : (5823879729 : ℕ)^85*10000000000000^69 ≤ 5137701824579^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5823879729 10000000000 5137701824579 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98102887/5000000000 : ℝ), (5495723527/10000000000 : ℝ), (5823879729/10000000000 : ℝ)] ![(788531167743/100000000000000 : ℝ), (2989653160607/6250000000000 : ℝ), (5137701824579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98102887/5000000000 : ℝ)|^85 ≤ (788531167743/100000000000000 : ℝ)^69
        have hw : |(-98102887/5000000000 : ℝ)|=(98102887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495723527/10000000000 : ℝ)|^85 ≤ (2989653160607/6250000000000 : ℝ)^69
        have hw : |(5495723527/10000000000 : ℝ)|=(5495723527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5823879729/10000000000 : ℝ)|^85 ≤ (5137701824579/10000000000000 : ℝ)^69
        have hw : |(5823879729/10000000000 : ℝ)|=(5823879729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5823879729/10000000000 : ℝ)*x 0 + (-98102887/5000000000 : ℝ)*x 1 + (5495723527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5823879729/10000000000 : ℝ)^85 ≤ (5137701824579/10000000000000 : ℝ)^69 := by
    have hnat : (5823879729 : ℕ)^85*10000000000000^69 ≤ 5137701824579^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5823879729 10000000000 5137701824579 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98102887/5000000000 : ℝ)^85 ≤ (788531167743/100000000000000 : ℝ)^69 := by
    have hnat : (98102887 : ℕ)^85*100000000000000^69 ≤ 788531167743^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98102887 5000000000 788531167743 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495723527/10000000000 : ℝ)^85 ≤ (2989653160607/6250000000000 : ℝ)^69 := by
    have hnat : (5495723527 : ℕ)^85*6250000000000^69 ≤ 2989653160607^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495723527 10000000000 2989653160607 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5823879729/10000000000 : ℝ), (-98102887/5000000000 : ℝ), (5495723527/10000000000 : ℝ)] ![(5137701824579/10000000000000 : ℝ), (788531167743/100000000000000 : ℝ), (2989653160607/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5823879729/10000000000 : ℝ)|^85 ≤ (5137701824579/10000000000000 : ℝ)^69
        have hw : |(5823879729/10000000000 : ℝ)|=(5823879729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98102887/5000000000 : ℝ)|^85 ≤ (788531167743/100000000000000 : ℝ)^69
        have hw : |(-98102887/5000000000 : ℝ)|=(98102887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495723527/10000000000 : ℝ)|^85 ≤ (2989653160607/6250000000000 : ℝ)^69
        have hw : |(5495723527/10000000000 : ℝ)|=(5495723527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5495723527/10000000000 : ℝ)*x 0 + (5823879729/10000000000 : ℝ)*x 1 + (-98102887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495723527/10000000000 : ℝ)^85 ≤ (2989653160607/6250000000000 : ℝ)^69 := by
    have hnat : (5495723527 : ℕ)^85*6250000000000^69 ≤ 2989653160607^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495723527 10000000000 2989653160607 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5823879729/10000000000 : ℝ)^85 ≤ (5137701824579/10000000000000 : ℝ)^69 := by
    have hnat : (5823879729 : ℕ)^85*10000000000000^69 ≤ 5137701824579^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5823879729 10000000000 5137701824579 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98102887/5000000000 : ℝ)^85 ≤ (788531167743/100000000000000 : ℝ)^69 := by
    have hnat : (98102887 : ℕ)^85*100000000000000^69 ≤ 788531167743^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98102887 5000000000 788531167743 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495723527/10000000000 : ℝ), (5823879729/10000000000 : ℝ), (-98102887/5000000000 : ℝ)] ![(2989653160607/6250000000000 : ℝ), (5137701824579/10000000000000 : ℝ), (788531167743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495723527/10000000000 : ℝ)|^85 ≤ (2989653160607/6250000000000 : ℝ)^69
        have hw : |(5495723527/10000000000 : ℝ)|=(5495723527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5823879729/10000000000 : ℝ)|^85 ≤ (5137701824579/10000000000000 : ℝ)^69
        have hw : |(5823879729/10000000000 : ℝ)|=(5823879729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98102887/5000000000 : ℝ)|^85 ≤ (788531167743/100000000000000 : ℝ)^69
        have hw : |(-98102887/5000000000 : ℝ)|=(98102887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1354029249/10000000000 : ℝ)*x 0 + (42528567/400000000 : ℝ)*x 1 + (8777487567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354029249/10000000000 : ℝ)^85 ≤ (8516603590863/100000000000000 : ℝ)^69 := by
    have hnat : (1354029249 : ℕ)^85*100000000000000^69 ≤ 8516603590863^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354029249 10000000000 8516603590863 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42528567/400000000 : ℝ)^85 ≤ (632280269191/10000000000000 : ℝ)^69 := by
    have hnat : (42528567 : ℕ)^85*10000000000000^69 ≤ 632280269191^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42528567 400000000 632280269191 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8777487567/10000000000 : ℝ)^85 ≤ (17032118740033/20000000000000 : ℝ)^69 := by
    have hnat : (8777487567 : ℕ)^85*20000000000000^69 ≤ 17032118740033^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8777487567 10000000000 17032118740033 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1354029249/10000000000 : ℝ), (42528567/400000000 : ℝ), (8777487567/10000000000 : ℝ)] ![(8516603590863/100000000000000 : ℝ), (632280269191/10000000000000 : ℝ), (17032118740033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1354029249/10000000000 : ℝ)|^85 ≤ (8516603590863/100000000000000 : ℝ)^69
        have hw : |(-1354029249/10000000000 : ℝ)|=(1354029249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42528567/400000000 : ℝ)|^85 ≤ (632280269191/10000000000000 : ℝ)^69
        have hw : |(42528567/400000000 : ℝ)|=(42528567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8777487567/10000000000 : ℝ)|^85 ≤ (17032118740033/20000000000000 : ℝ)^69
        have hw : |(8777487567/10000000000 : ℝ)|=(8777487567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4147144929/10000000000 : ℝ)*x 0 + (-14248767/500000000 : ℝ)*x 1 + (7043402291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4147144929/10000000000 : ℝ)^85 ≤ (845378810029/2500000000000 : ℝ)^69 := by
    have hnat : (4147144929 : ℕ)^85*2500000000000^69 ≤ 845378810029^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147144929 10000000000 845378810029 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14248767/500000000 : ℝ)^85 ≤ (1248825397193/100000000000000 : ℝ)^69 := by
    have hnat : (14248767 : ℕ)^85*100000000000000^69 ≤ 1248825397193^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14248767 500000000 1248825397193 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7043402291/10000000000 : ℝ)^85 ≤ (64936022186443/100000000000000 : ℝ)^69 := by
    have hnat : (7043402291 : ℕ)^85*100000000000000^69 ≤ 64936022186443^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7043402291 10000000000 64936022186443 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4147144929/10000000000 : ℝ), (-14248767/500000000 : ℝ), (7043402291/10000000000 : ℝ)] ![(845378810029/2500000000000 : ℝ), (1248825397193/100000000000000 : ℝ), (64936022186443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4147144929/10000000000 : ℝ)|^85 ≤ (845378810029/2500000000000 : ℝ)^69
        have hw : |(4147144929/10000000000 : ℝ)|=(4147144929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14248767/500000000 : ℝ)|^85 ≤ (1248825397193/100000000000000 : ℝ)^69
        have hw : |(-14248767/500000000 : ℝ)|=(14248767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7043402291/10000000000 : ℝ)|^85 ≤ (64936022186443/100000000000000 : ℝ)^69
        have hw : |(7043402291/10000000000 : ℝ)|=(7043402291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (430662293/2000000000 : ℝ)*x 0 + (8756569193/10000000000 : ℝ)*x 1 + (-4308479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430662293/2000000000 : ℝ)^85 ≤ (3770552326789/25000000000000 : ℝ)^69 := by
    have hnat : (430662293 : ℕ)^85*25000000000000^69 ≤ 3770552326789^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430662293 2000000000 3770552326789 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8756569193/10000000000 : ℝ)^85 ≤ (530691548361/625000000000 : ℝ)^69 := by
    have hnat : (8756569193 : ℕ)^85*625000000000^69 ≤ 530691548361^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8756569193 10000000000 530691548361 625000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4308479/10000000000 : ℝ)^85 ≤ (3571473003/50000000000000 : ℝ)^69 := by
    have hnat : (4308479 : ℕ)^85*50000000000000^69 ≤ 3571473003^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308479 10000000000 3571473003 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430662293/2000000000 : ℝ), (8756569193/10000000000 : ℝ), (-4308479/10000000000 : ℝ)] ![(3770552326789/25000000000000 : ℝ), (530691548361/625000000000 : ℝ), (3571473003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430662293/2000000000 : ℝ)|^85 ≤ (3770552326789/25000000000000 : ℝ)^69
        have hw : |(430662293/2000000000 : ℝ)|=(430662293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8756569193/10000000000 : ℝ)|^85 ≤ (530691548361/625000000000 : ℝ)^69
        have hw : |(8756569193/10000000000 : ℝ)|=(8756569193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4308479/10000000000 : ℝ)|^85 ≤ (3571473003/50000000000000 : ℝ)^69
        have hw : |(-4308479/10000000000 : ℝ)|=(4308479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2017483669/10000000000 : ℝ)*x 0 + (7138597467/10000000000 : ℝ)*x 1 + (169658347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017483669/10000000000 : ℝ)^85 ≤ (869934537977/6250000000000 : ℝ)^69 := by
    have hnat : (2017483669 : ℕ)^85*6250000000000^69 ≤ 869934537977^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017483669 10000000000 869934537977 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7138597467/10000000000 : ℝ)^85 ≤ (6601886555047/10000000000000 : ℝ)^69 := by
    have hnat : (7138597467 : ℕ)^85*10000000000000^69 ≤ 6601886555047^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7138597467 10000000000 6601886555047 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169658347/625000000 : ℝ)^85 ≤ (20062181824671/100000000000000 : ℝ)^69 := by
    have hnat : (169658347 : ℕ)^85*100000000000000^69 ≤ 20062181824671^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169658347 625000000 20062181824671 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2017483669/10000000000 : ℝ), (7138597467/10000000000 : ℝ), (169658347/625000000 : ℝ)] ![(869934537977/6250000000000 : ℝ), (6601886555047/10000000000000 : ℝ), (20062181824671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2017483669/10000000000 : ℝ)|^85 ≤ (869934537977/6250000000000 : ℝ)^69
        have hw : |(2017483669/10000000000 : ℝ)|=(2017483669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7138597467/10000000000 : ℝ)|^85 ≤ (6601886555047/10000000000000 : ℝ)^69
        have hw : |(7138597467/10000000000 : ℝ)|=(7138597467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169658347/625000000 : ℝ)|^85 ≤ (20062181824671/100000000000000 : ℝ)^69
        have hw : |(169658347/625000000 : ℝ)|=(169658347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4308479/10000000000 : ℝ)*x 0 + (430662293/2000000000 : ℝ)*x 1 + (8756569193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308479/10000000000 : ℝ)^85 ≤ (3571473003/50000000000000 : ℝ)^69 := by
    have hnat : (4308479 : ℕ)^85*50000000000000^69 ≤ 3571473003^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308479 10000000000 3571473003 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430662293/2000000000 : ℝ)^85 ≤ (3770552326789/25000000000000 : ℝ)^69 := by
    have hnat : (430662293 : ℕ)^85*25000000000000^69 ≤ 3770552326789^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430662293 2000000000 3770552326789 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8756569193/10000000000 : ℝ)^85 ≤ (530691548361/625000000000 : ℝ)^69 := by
    have hnat : (8756569193 : ℕ)^85*625000000000^69 ≤ 530691548361^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8756569193 10000000000 530691548361 625000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4308479/10000000000 : ℝ), (430662293/2000000000 : ℝ), (8756569193/10000000000 : ℝ)] ![(3571473003/50000000000000 : ℝ), (3770552326789/25000000000000 : ℝ), (530691548361/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4308479/10000000000 : ℝ)|^85 ≤ (3571473003/50000000000000 : ℝ)^69
        have hw : |(-4308479/10000000000 : ℝ)|=(4308479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430662293/2000000000 : ℝ)|^85 ≤ (3770552326789/25000000000000 : ℝ)^69
        have hw : |(430662293/2000000000 : ℝ)|=(430662293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8756569193/10000000000 : ℝ)|^85 ≤ (530691548361/625000000000 : ℝ)^69
        have hw : |(8756569193/10000000000 : ℝ)|=(8756569193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8777487567/10000000000 : ℝ)*x 0 + (-1354029249/10000000000 : ℝ)*x 1 + (42528567/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8777487567/10000000000 : ℝ)^85 ≤ (17032118740033/20000000000000 : ℝ)^69 := by
    have hnat : (8777487567 : ℕ)^85*20000000000000^69 ≤ 17032118740033^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8777487567 10000000000 17032118740033 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354029249/10000000000 : ℝ)^85 ≤ (8516603590863/100000000000000 : ℝ)^69 := by
    have hnat : (1354029249 : ℕ)^85*100000000000000^69 ≤ 8516603590863^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354029249 10000000000 8516603590863 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42528567/400000000 : ℝ)^85 ≤ (632280269191/10000000000000 : ℝ)^69 := by
    have hnat : (42528567 : ℕ)^85*10000000000000^69 ≤ 632280269191^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42528567 400000000 632280269191 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8777487567/10000000000 : ℝ), (-1354029249/10000000000 : ℝ), (42528567/400000000 : ℝ)] ![(17032118740033/20000000000000 : ℝ), (8516603590863/100000000000000 : ℝ), (632280269191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8777487567/10000000000 : ℝ)|^85 ≤ (17032118740033/20000000000000 : ℝ)^69
        have hw : |(8777487567/10000000000 : ℝ)|=(8777487567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1354029249/10000000000 : ℝ)|^85 ≤ (8516603590863/100000000000000 : ℝ)^69
        have hw : |(-1354029249/10000000000 : ℝ)|=(1354029249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42528567/400000000 : ℝ)|^85 ≤ (632280269191/10000000000000 : ℝ)^69
        have hw : |(42528567/400000000 : ℝ)|=(42528567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7043402291/10000000000 : ℝ)*x 0 + (4147144929/10000000000 : ℝ)*x 1 + (-14248767/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7043402291/10000000000 : ℝ)^85 ≤ (64936022186443/100000000000000 : ℝ)^69 := by
    have hnat : (7043402291 : ℕ)^85*100000000000000^69 ≤ 64936022186443^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7043402291 10000000000 64936022186443 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147144929/10000000000 : ℝ)^85 ≤ (845378810029/2500000000000 : ℝ)^69 := by
    have hnat : (4147144929 : ℕ)^85*2500000000000^69 ≤ 845378810029^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147144929 10000000000 845378810029 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14248767/500000000 : ℝ)^85 ≤ (1248825397193/100000000000000 : ℝ)^69 := by
    have hnat : (14248767 : ℕ)^85*100000000000000^69 ≤ 1248825397193^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14248767 500000000 1248825397193 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7043402291/10000000000 : ℝ), (4147144929/10000000000 : ℝ), (-14248767/500000000 : ℝ)] ![(64936022186443/100000000000000 : ℝ), (845378810029/2500000000000 : ℝ), (1248825397193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7043402291/10000000000 : ℝ)|^85 ≤ (64936022186443/100000000000000 : ℝ)^69
        have hw : |(7043402291/10000000000 : ℝ)|=(7043402291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147144929/10000000000 : ℝ)|^85 ≤ (845378810029/2500000000000 : ℝ)^69
        have hw : |(4147144929/10000000000 : ℝ)|=(4147144929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14248767/500000000 : ℝ)|^85 ≤ (1248825397193/100000000000000 : ℝ)^69
        have hw : |(-14248767/500000000 : ℝ)|=(14248767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (169658347/625000000 : ℝ)*x 0 + (2017483669/10000000000 : ℝ)*x 1 + (7138597467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169658347/625000000 : ℝ)^85 ≤ (20062181824671/100000000000000 : ℝ)^69 := by
    have hnat : (169658347 : ℕ)^85*100000000000000^69 ≤ 20062181824671^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169658347 625000000 20062181824671 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017483669/10000000000 : ℝ)^85 ≤ (869934537977/6250000000000 : ℝ)^69 := by
    have hnat : (2017483669 : ℕ)^85*6250000000000^69 ≤ 869934537977^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017483669 10000000000 869934537977 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7138597467/10000000000 : ℝ)^85 ≤ (6601886555047/10000000000000 : ℝ)^69 := by
    have hnat : (7138597467 : ℕ)^85*10000000000000^69 ≤ 6601886555047^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7138597467 10000000000 6601886555047 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169658347/625000000 : ℝ), (2017483669/10000000000 : ℝ), (7138597467/10000000000 : ℝ)] ![(20062181824671/100000000000000 : ℝ), (869934537977/6250000000000 : ℝ), (6601886555047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169658347/625000000 : ℝ)|^85 ≤ (20062181824671/100000000000000 : ℝ)^69
        have hw : |(169658347/625000000 : ℝ)|=(169658347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017483669/10000000000 : ℝ)|^85 ≤ (869934537977/6250000000000 : ℝ)^69
        have hw : |(2017483669/10000000000 : ℝ)|=(2017483669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7138597467/10000000000 : ℝ)|^85 ≤ (6601886555047/10000000000000 : ℝ)^69
        have hw : |(7138597467/10000000000 : ℝ)|=(7138597467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-14248767/500000000 : ℝ)*x 0 + (7043402291/10000000000 : ℝ)*x 1 + (4147144929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14248767/500000000 : ℝ)^85 ≤ (1248825397193/100000000000000 : ℝ)^69 := by
    have hnat : (14248767 : ℕ)^85*100000000000000^69 ≤ 1248825397193^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14248767 500000000 1248825397193 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7043402291/10000000000 : ℝ)^85 ≤ (64936022186443/100000000000000 : ℝ)^69 := by
    have hnat : (7043402291 : ℕ)^85*100000000000000^69 ≤ 64936022186443^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7043402291 10000000000 64936022186443 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147144929/10000000000 : ℝ)^85 ≤ (845378810029/2500000000000 : ℝ)^69 := by
    have hnat : (4147144929 : ℕ)^85*2500000000000^69 ≤ 845378810029^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147144929 10000000000 845378810029 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14248767/500000000 : ℝ), (7043402291/10000000000 : ℝ), (4147144929/10000000000 : ℝ)] ![(1248825397193/100000000000000 : ℝ), (64936022186443/100000000000000 : ℝ), (845378810029/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14248767/500000000 : ℝ)|^85 ≤ (1248825397193/100000000000000 : ℝ)^69
        have hw : |(-14248767/500000000 : ℝ)|=(14248767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7043402291/10000000000 : ℝ)|^85 ≤ (64936022186443/100000000000000 : ℝ)^69
        have hw : |(7043402291/10000000000 : ℝ)|=(7043402291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147144929/10000000000 : ℝ)|^85 ≤ (845378810029/2500000000000 : ℝ)^69
        have hw : |(4147144929/10000000000 : ℝ)|=(4147144929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8756569193/10000000000 : ℝ)*x 0 + (-4308479/10000000000 : ℝ)*x 1 + (430662293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8756569193/10000000000 : ℝ)^85 ≤ (530691548361/625000000000 : ℝ)^69 := by
    have hnat : (8756569193 : ℕ)^85*625000000000^69 ≤ 530691548361^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8756569193 10000000000 530691548361 625000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4308479/10000000000 : ℝ)^85 ≤ (3571473003/50000000000000 : ℝ)^69 := by
    have hnat : (4308479 : ℕ)^85*50000000000000^69 ≤ 3571473003^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308479 10000000000 3571473003 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430662293/2000000000 : ℝ)^85 ≤ (3770552326789/25000000000000 : ℝ)^69 := by
    have hnat : (430662293 : ℕ)^85*25000000000000^69 ≤ 3770552326789^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430662293 2000000000 3770552326789 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8756569193/10000000000 : ℝ), (-4308479/10000000000 : ℝ), (430662293/2000000000 : ℝ)] ![(530691548361/625000000000 : ℝ), (3571473003/50000000000000 : ℝ), (3770552326789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8756569193/10000000000 : ℝ)|^85 ≤ (530691548361/625000000000 : ℝ)^69
        have hw : |(8756569193/10000000000 : ℝ)|=(8756569193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4308479/10000000000 : ℝ)|^85 ≤ (3571473003/50000000000000 : ℝ)^69
        have hw : |(-4308479/10000000000 : ℝ)|=(4308479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(430662293/2000000000 : ℝ)|^85 ≤ (3770552326789/25000000000000 : ℝ)^69
        have hw : |(430662293/2000000000 : ℝ)|=(430662293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (42528567/400000000 : ℝ)*x 0 + (8777487567/10000000000 : ℝ)*x 1 + (-1354029249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42528567/400000000 : ℝ)^85 ≤ (632280269191/10000000000000 : ℝ)^69 := by
    have hnat : (42528567 : ℕ)^85*10000000000000^69 ≤ 632280269191^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42528567 400000000 632280269191 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8777487567/10000000000 : ℝ)^85 ≤ (17032118740033/20000000000000 : ℝ)^69 := by
    have hnat : (8777487567 : ℕ)^85*20000000000000^69 ≤ 17032118740033^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8777487567 10000000000 17032118740033 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354029249/10000000000 : ℝ)^85 ≤ (8516603590863/100000000000000 : ℝ)^69 := by
    have hnat : (1354029249 : ℕ)^85*100000000000000^69 ≤ 8516603590863^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354029249 10000000000 8516603590863 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42528567/400000000 : ℝ), (8777487567/10000000000 : ℝ), (-1354029249/10000000000 : ℝ)] ![(632280269191/10000000000000 : ℝ), (17032118740033/20000000000000 : ℝ), (8516603590863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42528567/400000000 : ℝ)|^85 ≤ (632280269191/10000000000000 : ℝ)^69
        have hw : |(42528567/400000000 : ℝ)|=(42528567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8777487567/10000000000 : ℝ)|^85 ≤ (17032118740033/20000000000000 : ℝ)^69
        have hw : |(8777487567/10000000000 : ℝ)|=(8777487567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1354029249/10000000000 : ℝ)|^85 ≤ (8516603590863/100000000000000 : ℝ)^69
        have hw : |(-1354029249/10000000000 : ℝ)|=(1354029249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s0_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7138597467/10000000000 : ℝ)*x 0 + (169658347/625000000 : ℝ)*x 1 + (2017483669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7138597467/10000000000 : ℝ)^85 ≤ (6601886555047/10000000000000 : ℝ)^69 := by
    have hnat : (7138597467 : ℕ)^85*10000000000000^69 ≤ 6601886555047^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7138597467 10000000000 6601886555047 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169658347/625000000 : ℝ)^85 ≤ (20062181824671/100000000000000 : ℝ)^69 := by
    have hnat : (169658347 : ℕ)^85*100000000000000^69 ≤ 20062181824671^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169658347 625000000 20062181824671 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017483669/10000000000 : ℝ)^85 ≤ (869934537977/6250000000000 : ℝ)^69 := by
    have hnat : (2017483669 : ℕ)^85*6250000000000^69 ≤ 869934537977^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017483669 10000000000 869934537977 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7138597467/10000000000 : ℝ), (169658347/625000000 : ℝ), (2017483669/10000000000 : ℝ)] ![(6601886555047/10000000000000 : ℝ), (20062181824671/100000000000000 : ℝ), (869934537977/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7138597467/10000000000 : ℝ)|^85 ≤ (6601886555047/10000000000000 : ℝ)^69
        have hw : |(7138597467/10000000000 : ℝ)|=(7138597467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169658347/625000000 : ℝ)|^85 ≤ (20062181824671/100000000000000 : ℝ)^69
        have hw : |(169658347/625000000 : ℝ)|=(169658347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017483669/10000000000 : ℝ)|^85 ≤ (869934537977/6250000000000 : ℝ)^69
        have hw : |(2017483669/10000000000 : ℝ)|=(2017483669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-246869709/2500000000 : ℝ)*x 0 + (5421058187/10000000000 : ℝ)*x 1 + (2717875179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246869709/2500000000 : ℝ)^85 ≤ (1443161154189/25000000000000 : ℝ)^69 := by
    have hnat : (246869709 : ℕ)^85*25000000000000^69 ≤ 1443161154189^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246869709 2500000000 1443161154189 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421058187/10000000000 : ℝ)^85 ≤ (1881405437843/4000000000000 : ℝ)^69 := by
    have hnat : (5421058187 : ℕ)^85*4000000000000^69 ≤ 1881405437843^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421058187 10000000000 1881405437843 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717875179/5000000000 : ℝ)^85 ≤ (4719221941921/10000000000000 : ℝ)^69 := by
    have hnat : (2717875179 : ℕ)^85*10000000000000^69 ≤ 4719221941921^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717875179 5000000000 4719221941921 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246869709/2500000000 : ℝ), (5421058187/10000000000 : ℝ), (2717875179/5000000000 : ℝ)] ![(1443161154189/25000000000000 : ℝ), (1881405437843/4000000000000 : ℝ), (4719221941921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246869709/2500000000 : ℝ)|^85 ≤ (1443161154189/25000000000000 : ℝ)^69
        have hw : |(-246869709/2500000000 : ℝ)|=(246869709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421058187/10000000000 : ℝ)|^85 ≤ (1881405437843/4000000000000 : ℝ)^69
        have hw : |(5421058187/10000000000 : ℝ)|=(5421058187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717875179/5000000000 : ℝ)|^85 ≤ (4719221941921/10000000000000 : ℝ)^69
        have hw : |(2717875179/5000000000 : ℝ)|=(2717875179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2717875299/5000000000 : ℝ)*x 0 + (-987478717/10000000000 : ℝ)*x 1 + (5421058027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717875299/5000000000 : ℝ)^85 ≤ (4719222198601/10000000000000 : ℝ)^69 := by
    have hnat : (2717875299 : ℕ)^85*10000000000000^69 ≤ 4719222198601^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717875299 5000000000 4719222198601 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987478717/10000000000 : ℝ)^85 ≤ (5772643759789/100000000000000 : ℝ)^69 := by
    have hnat : (987478717 : ℕ)^85*100000000000000^69 ≤ 5772643759789^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987478717 10000000000 5772643759789 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421058027/10000000000 : ℝ)^85 ≤ (47035134235949/100000000000000 : ℝ)^69 := by
    have hnat : (5421058027 : ℕ)^85*100000000000000^69 ≤ 47035134235949^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421058027 10000000000 47035134235949 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717875299/5000000000 : ℝ), (-987478717/10000000000 : ℝ), (5421058027/10000000000 : ℝ)] ![(4719222198601/10000000000000 : ℝ), (5772643759789/100000000000000 : ℝ), (47035134235949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717875299/5000000000 : ℝ)|^85 ≤ (4719222198601/10000000000000 : ℝ)^69
        have hw : |(2717875299/5000000000 : ℝ)|=(2717875299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987478717/10000000000 : ℝ)|^85 ≤ (5772643759789/100000000000000 : ℝ)^69
        have hw : |(-987478717/10000000000 : ℝ)|=(987478717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421058027/10000000000 : ℝ)|^85 ≤ (47035134235949/100000000000000 : ℝ)^69
        have hw : |(5421058027/10000000000 : ℝ)|=(5421058027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5421057833/10000000000 : ℝ)*x 0 + (339734419/625000000 : ℝ)*x 1 + (-15429357/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421057833/10000000000 : ℝ)^85 ≤ (47035132162421/100000000000000 : ℝ)^69 := by
    have hnat : (5421057833 : ℕ)^85*100000000000000^69 ≤ 47035132162421^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421057833 10000000000 47035132162421 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339734419/625000000 : ℝ)^85 ≤ (47192223119679/100000000000000 : ℝ)^69 := by
    have hnat : (339734419 : ℕ)^85*100000000000000^69 ≤ 47192223119679^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339734419 625000000 47192223119679 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15429357/156250000 : ℝ)^85 ≤ (1443161175793/25000000000000 : ℝ)^69 := by
    have hnat : (15429357 : ℕ)^85*25000000000000^69 ≤ 1443161175793^69*156250000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15429357 156250000 1443161175793 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421057833/10000000000 : ℝ), (339734419/625000000 : ℝ), (-15429357/156250000 : ℝ)] ![(47035132162421/100000000000000 : ℝ), (47192223119679/100000000000000 : ℝ), (1443161175793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421057833/10000000000 : ℝ)|^85 ≤ (47035132162421/100000000000000 : ℝ)^69
        have hw : |(5421057833/10000000000 : ℝ)|=(5421057833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339734419/625000000 : ℝ)|^85 ≤ (47192223119679/100000000000000 : ℝ)^69
        have hw : |(339734419/625000000 : ℝ)|=(339734419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15429357/156250000 : ℝ)|^85 ≤ (1443161175793/25000000000000 : ℝ)^69
        have hw : |(-15429357/156250000 : ℝ)|=(15429357/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-883046747/10000000000 : ℝ)*x 0 + (899735427/2000000000 : ℝ)*x 1 + (3194677571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883046747/10000000000 : ℝ)^85 ≤ (1006014204209/20000000000000 : ℝ)^69 := by
    have hnat : (883046747 : ℕ)^85*20000000000000^69 ≤ 1006014204209^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883046747 10000000000 1006014204209 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899735427/2000000000 : ℝ)^85 ≤ (37380123078607/100000000000000 : ℝ)^69 := by
    have hnat : (899735427 : ℕ)^85*100000000000000^69 ≤ 37380123078607^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899735427 2000000000 37380123078607 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194677571/5000000000 : ℝ)^85 ≤ (57589805880989/100000000000000 : ℝ)^69 := by
    have hnat : (3194677571 : ℕ)^85*100000000000000^69 ≤ 57589805880989^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194677571 5000000000 57589805880989 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-883046747/10000000000 : ℝ), (899735427/2000000000 : ℝ), (3194677571/5000000000 : ℝ)] ![(1006014204209/20000000000000 : ℝ), (37380123078607/100000000000000 : ℝ), (57589805880989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-883046747/10000000000 : ℝ)|^85 ≤ (1006014204209/20000000000000 : ℝ)^69
        have hw : |(-883046747/10000000000 : ℝ)|=(883046747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899735427/2000000000 : ℝ)|^85 ≤ (37380123078607/100000000000000 : ℝ)^69
        have hw : |(899735427/2000000000 : ℝ)|=(899735427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194677571/5000000000 : ℝ)|^85 ≤ (57589805880989/100000000000000 : ℝ)^69
        have hw : |(3194677571/5000000000 : ℝ)|=(3194677571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5670074667/10000000000 : ℝ)*x 0 + (-41353653/2500000000 : ℝ)*x 1 + (1132896337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5670074667/10000000000 : ℝ)^85 ≤ (49710707463629/100000000000000 : ℝ)^69 := by
    have hnat : (5670074667 : ℕ)^85*100000000000000^69 ≤ 49710707463629^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670074667 10000000000 49710707463629 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41353653/2500000000 : ℝ)^85 ≤ (638983362983/100000000000000 : ℝ)^69 := by
    have hnat : (41353653 : ℕ)^85*100000000000000^69 ≤ 638983362983^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41353653 2500000000 638983362983 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132896337/2000000000 : ℝ)^85 ≤ (24825154580157/50000000000000 : ℝ)^69 := by
    have hnat : (1132896337 : ℕ)^85*50000000000000^69 ≤ 24825154580157^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132896337 2000000000 24825154580157 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5670074667/10000000000 : ℝ), (-41353653/2500000000 : ℝ), (1132896337/2000000000 : ℝ)] ![(49710707463629/100000000000000 : ℝ), (638983362983/100000000000000 : ℝ), (24825154580157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5670074667/10000000000 : ℝ)|^85 ≤ (49710707463629/100000000000000 : ℝ)^69
        have hw : |(5670074667/10000000000 : ℝ)|=(5670074667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41353653/2500000000 : ℝ)|^85 ≤ (638983362983/100000000000000 : ℝ)^69
        have hw : |(-41353653/2500000000 : ℝ)|=(41353653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132896337/2000000000 : ℝ)|^85 ≤ (24825154580157/50000000000000 : ℝ)^69
        have hw : |(1132896337/2000000000 : ℝ)|=(1132896337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (171787707/400000000 : ℝ)*x 0 + (54587457/78125000 : ℝ)*x 1 + (-28186361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171787707/400000000 : ℝ)^85 ≤ (2206454177423/6250000000000 : ℝ)^69 := by
    have hnat : (171787707 : ℕ)^85*6250000000000^69 ≤ 2206454177423^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171787707 400000000 2206454177423 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54587457/78125000 : ℝ)^85 ≤ (64298248300647/100000000000000 : ℝ)^69 := by
    have hnat : (54587457 : ℕ)^85*100000000000000^69 ≤ 64298248300647^69*78125000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54587457 78125000 64298248300647 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28186361/2500000000 : ℝ)^85 ≤ (79696969727/20000000000000 : ℝ)^69 := by
    have hnat : (28186361 : ℕ)^85*20000000000000^69 ≤ 79696969727^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28186361 2500000000 79696969727 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171787707/400000000 : ℝ), (54587457/78125000 : ℝ), (-28186361/2500000000 : ℝ)] ![(2206454177423/6250000000000 : ℝ), (64298248300647/100000000000000 : ℝ), (79696969727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171787707/400000000 : ℝ)|^85 ≤ (2206454177423/6250000000000 : ℝ)^69
        have hw : |(171787707/400000000 : ℝ)|=(171787707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54587457/78125000 : ℝ)|^85 ≤ (64298248300647/100000000000000 : ℝ)^69
        have hw : |(54587457/78125000 : ℝ)|=(54587457/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28186361/2500000000 : ℝ)|^85 ≤ (79696969727/20000000000000 : ℝ)^69
        have hw : |(-28186361/2500000000 : ℝ)|=(28186361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1788502889/5000000000 : ℝ)*x 0 + (159462959/312500000 : ℝ)*x 1 + (3574608791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788502889/5000000000 : ℝ)^85 ≤ (1761440516493/6250000000000 : ℝ)^69 := by
    have hnat : (1788502889 : ℕ)^85*6250000000000^69 ≤ 1761440516493^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788502889 5000000000 1761440516493 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159462959/312500000 : ℝ)^85 ≤ (21828583343691/50000000000000 : ℝ)^69 := by
    have hnat : (159462959 : ℕ)^85*50000000000000^69 ≤ 21828583343691^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159462959 312500000 21828583343691 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3574608791/10000000000 : ℝ)^85 ≤ (14079892514997/50000000000000 : ℝ)^69 := by
    have hnat : (3574608791 : ℕ)^85*50000000000000^69 ≤ 14079892514997^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574608791 10000000000 14079892514997 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1788502889/5000000000 : ℝ), (159462959/312500000 : ℝ), (3574608791/10000000000 : ℝ)] ![(1761440516493/6250000000000 : ℝ), (21828583343691/50000000000000 : ℝ), (14079892514997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1788502889/5000000000 : ℝ)|^85 ≤ (1761440516493/6250000000000 : ℝ)^69
        have hw : |(1788502889/5000000000 : ℝ)|=(1788502889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(159462959/312500000 : ℝ)|^85 ≤ (21828583343691/50000000000000 : ℝ)^69
        have hw : |(159462959/312500000 : ℝ)|=(159462959/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3574608791/10000000000 : ℝ)|^85 ≤ (14079892514997/50000000000000 : ℝ)^69
        have hw : |(3574608791/10000000000 : ℝ)|=(3574608791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-28186361/2500000000 : ℝ)*x 0 + (171787707/400000000 : ℝ)*x 1 + (54587457/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28186361/2500000000 : ℝ)^85 ≤ (79696969727/20000000000000 : ℝ)^69 := by
    have hnat : (28186361 : ℕ)^85*20000000000000^69 ≤ 79696969727^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28186361 2500000000 79696969727 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171787707/400000000 : ℝ)^85 ≤ (2206454177423/6250000000000 : ℝ)^69 := by
    have hnat : (171787707 : ℕ)^85*6250000000000^69 ≤ 2206454177423^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171787707 400000000 2206454177423 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54587457/78125000 : ℝ)^85 ≤ (64298248300647/100000000000000 : ℝ)^69 := by
    have hnat : (54587457 : ℕ)^85*100000000000000^69 ≤ 64298248300647^69*78125000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54587457 78125000 64298248300647 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28186361/2500000000 : ℝ), (171787707/400000000 : ℝ), (54587457/78125000 : ℝ)] ![(79696969727/20000000000000 : ℝ), (2206454177423/6250000000000 : ℝ), (64298248300647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28186361/2500000000 : ℝ)|^85 ≤ (79696969727/20000000000000 : ℝ)^69
        have hw : |(-28186361/2500000000 : ℝ)|=(28186361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171787707/400000000 : ℝ)|^85 ≤ (2206454177423/6250000000000 : ℝ)^69
        have hw : |(171787707/400000000 : ℝ)|=(171787707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54587457/78125000 : ℝ)|^85 ≤ (64298248300647/100000000000000 : ℝ)^69
        have hw : |(54587457/78125000 : ℝ)|=(54587457/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3194677571/5000000000 : ℝ)*x 0 + (-883046747/10000000000 : ℝ)*x 1 + (899735427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3194677571/5000000000 : ℝ)^85 ≤ (57589805880989/100000000000000 : ℝ)^69 := by
    have hnat : (3194677571 : ℕ)^85*100000000000000^69 ≤ 57589805880989^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194677571 5000000000 57589805880989 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883046747/10000000000 : ℝ)^85 ≤ (1006014204209/20000000000000 : ℝ)^69 := by
    have hnat : (883046747 : ℕ)^85*20000000000000^69 ≤ 1006014204209^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883046747 10000000000 1006014204209 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899735427/2000000000 : ℝ)^85 ≤ (37380123078607/100000000000000 : ℝ)^69 := by
    have hnat : (899735427 : ℕ)^85*100000000000000^69 ≤ 37380123078607^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899735427 2000000000 37380123078607 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3194677571/5000000000 : ℝ), (-883046747/10000000000 : ℝ), (899735427/2000000000 : ℝ)] ![(57589805880989/100000000000000 : ℝ), (1006014204209/20000000000000 : ℝ), (37380123078607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3194677571/5000000000 : ℝ)|^85 ≤ (57589805880989/100000000000000 : ℝ)^69
        have hw : |(3194677571/5000000000 : ℝ)|=(3194677571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883046747/10000000000 : ℝ)|^85 ≤ (1006014204209/20000000000000 : ℝ)^69
        have hw : |(-883046747/10000000000 : ℝ)|=(883046747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899735427/2000000000 : ℝ)|^85 ≤ (37380123078607/100000000000000 : ℝ)^69
        have hw : |(899735427/2000000000 : ℝ)|=(899735427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1132896337/2000000000 : ℝ)*x 0 + (5670074667/10000000000 : ℝ)*x 1 + (-41353653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132896337/2000000000 : ℝ)^85 ≤ (24825154580157/50000000000000 : ℝ)^69 := by
    have hnat : (1132896337 : ℕ)^85*50000000000000^69 ≤ 24825154580157^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132896337 2000000000 24825154580157 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5670074667/10000000000 : ℝ)^85 ≤ (49710707463629/100000000000000 : ℝ)^69 := by
    have hnat : (5670074667 : ℕ)^85*100000000000000^69 ≤ 49710707463629^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670074667 10000000000 49710707463629 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41353653/2500000000 : ℝ)^85 ≤ (638983362983/100000000000000 : ℝ)^69 := by
    have hnat : (41353653 : ℕ)^85*100000000000000^69 ≤ 638983362983^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41353653 2500000000 638983362983 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1132896337/2000000000 : ℝ), (5670074667/10000000000 : ℝ), (-41353653/2500000000 : ℝ)] ![(24825154580157/50000000000000 : ℝ), (49710707463629/100000000000000 : ℝ), (638983362983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1132896337/2000000000 : ℝ)|^85 ≤ (24825154580157/50000000000000 : ℝ)^69
        have hw : |(1132896337/2000000000 : ℝ)|=(1132896337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5670074667/10000000000 : ℝ)|^85 ≤ (49710707463629/100000000000000 : ℝ)^69
        have hw : |(5670074667/10000000000 : ℝ)|=(5670074667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41353653/2500000000 : ℝ)|^85 ≤ (638983362983/100000000000000 : ℝ)^69
        have hw : |(-41353653/2500000000 : ℝ)|=(41353653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3574608791/10000000000 : ℝ)*x 0 + (1788502889/5000000000 : ℝ)*x 1 + (159462959/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3574608791/10000000000 : ℝ)^85 ≤ (14079892514997/50000000000000 : ℝ)^69 := by
    have hnat : (3574608791 : ℕ)^85*50000000000000^69 ≤ 14079892514997^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574608791 10000000000 14079892514997 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788502889/5000000000 : ℝ)^85 ≤ (1761440516493/6250000000000 : ℝ)^69 := by
    have hnat : (1788502889 : ℕ)^85*6250000000000^69 ≤ 1761440516493^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788502889 5000000000 1761440516493 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159462959/312500000 : ℝ)^85 ≤ (21828583343691/50000000000000 : ℝ)^69 := by
    have hnat : (159462959 : ℕ)^85*50000000000000^69 ≤ 21828583343691^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159462959 312500000 21828583343691 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3574608791/10000000000 : ℝ), (1788502889/5000000000 : ℝ), (159462959/312500000 : ℝ)] ![(14079892514997/50000000000000 : ℝ), (1761440516493/6250000000000 : ℝ), (21828583343691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3574608791/10000000000 : ℝ)|^85 ≤ (14079892514997/50000000000000 : ℝ)^69
        have hw : |(3574608791/10000000000 : ℝ)|=(3574608791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1788502889/5000000000 : ℝ)|^85 ≤ (1761440516493/6250000000000 : ℝ)^69
        have hw : |(1788502889/5000000000 : ℝ)|=(1788502889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159462959/312500000 : ℝ)|^85 ≤ (21828583343691/50000000000000 : ℝ)^69
        have hw : |(159462959/312500000 : ℝ)|=(159462959/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-41353653/2500000000 : ℝ)*x 0 + (1132896337/2000000000 : ℝ)*x 1 + (5670074667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41353653/2500000000 : ℝ)^85 ≤ (638983362983/100000000000000 : ℝ)^69 := by
    have hnat : (41353653 : ℕ)^85*100000000000000^69 ≤ 638983362983^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41353653 2500000000 638983362983 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132896337/2000000000 : ℝ)^85 ≤ (24825154580157/50000000000000 : ℝ)^69 := by
    have hnat : (1132896337 : ℕ)^85*50000000000000^69 ≤ 24825154580157^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132896337 2000000000 24825154580157 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5670074667/10000000000 : ℝ)^85 ≤ (49710707463629/100000000000000 : ℝ)^69 := by
    have hnat : (5670074667 : ℕ)^85*100000000000000^69 ≤ 49710707463629^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670074667 10000000000 49710707463629 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41353653/2500000000 : ℝ), (1132896337/2000000000 : ℝ), (5670074667/10000000000 : ℝ)] ![(638983362983/100000000000000 : ℝ), (24825154580157/50000000000000 : ℝ), (49710707463629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41353653/2500000000 : ℝ)|^85 ≤ (638983362983/100000000000000 : ℝ)^69
        have hw : |(-41353653/2500000000 : ℝ)|=(41353653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132896337/2000000000 : ℝ)|^85 ≤ (24825154580157/50000000000000 : ℝ)^69
        have hw : |(1132896337/2000000000 : ℝ)|=(1132896337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5670074667/10000000000 : ℝ)|^85 ≤ (49710707463629/100000000000000 : ℝ)^69
        have hw : |(5670074667/10000000000 : ℝ)|=(5670074667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54587457/78125000 : ℝ)*x 0 + (-28186361/2500000000 : ℝ)*x 1 + (171787707/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54587457/78125000 : ℝ)^85 ≤ (64298248300647/100000000000000 : ℝ)^69 := by
    have hnat : (54587457 : ℕ)^85*100000000000000^69 ≤ 64298248300647^69*78125000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54587457 78125000 64298248300647 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28186361/2500000000 : ℝ)^85 ≤ (79696969727/20000000000000 : ℝ)^69 := by
    have hnat : (28186361 : ℕ)^85*20000000000000^69 ≤ 79696969727^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28186361 2500000000 79696969727 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171787707/400000000 : ℝ)^85 ≤ (2206454177423/6250000000000 : ℝ)^69 := by
    have hnat : (171787707 : ℕ)^85*6250000000000^69 ≤ 2206454177423^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171787707 400000000 2206454177423 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54587457/78125000 : ℝ), (-28186361/2500000000 : ℝ), (171787707/400000000 : ℝ)] ![(64298248300647/100000000000000 : ℝ), (79696969727/20000000000000 : ℝ), (2206454177423/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54587457/78125000 : ℝ)|^85 ≤ (64298248300647/100000000000000 : ℝ)^69
        have hw : |(54587457/78125000 : ℝ)|=(54587457/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28186361/2500000000 : ℝ)|^85 ≤ (79696969727/20000000000000 : ℝ)^69
        have hw : |(-28186361/2500000000 : ℝ)|=(28186361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171787707/400000000 : ℝ)|^85 ≤ (2206454177423/6250000000000 : ℝ)^69
        have hw : |(171787707/400000000 : ℝ)|=(171787707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (899735427/2000000000 : ℝ)*x 0 + (3194677571/5000000000 : ℝ)*x 1 + (-883046747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899735427/2000000000 : ℝ)^85 ≤ (37380123078607/100000000000000 : ℝ)^69 := by
    have hnat : (899735427 : ℕ)^85*100000000000000^69 ≤ 37380123078607^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899735427 2000000000 37380123078607 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3194677571/5000000000 : ℝ)^85 ≤ (57589805880989/100000000000000 : ℝ)^69 := by
    have hnat : (3194677571 : ℕ)^85*100000000000000^69 ≤ 57589805880989^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194677571 5000000000 57589805880989 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883046747/10000000000 : ℝ)^85 ≤ (1006014204209/20000000000000 : ℝ)^69 := by
    have hnat : (883046747 : ℕ)^85*20000000000000^69 ≤ 1006014204209^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883046747 10000000000 1006014204209 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899735427/2000000000 : ℝ), (3194677571/5000000000 : ℝ), (-883046747/10000000000 : ℝ)] ![(37380123078607/100000000000000 : ℝ), (57589805880989/100000000000000 : ℝ), (1006014204209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899735427/2000000000 : ℝ)|^85 ≤ (37380123078607/100000000000000 : ℝ)^69
        have hw : |(899735427/2000000000 : ℝ)|=(899735427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3194677571/5000000000 : ℝ)|^85 ≤ (57589805880989/100000000000000 : ℝ)^69
        have hw : |(3194677571/5000000000 : ℝ)|=(3194677571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883046747/10000000000 : ℝ)|^85 ≤ (1006014204209/20000000000000 : ℝ)^69
        have hw : |(-883046747/10000000000 : ℝ)|=(883046747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324087_s1_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (159462959/312500000 : ℝ)*x 0 + (3574608791/10000000000 : ℝ)*x 1 + (1788502889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159462959/312500000 : ℝ)^85 ≤ (21828583343691/50000000000000 : ℝ)^69 := by
    have hnat : (159462959 : ℕ)^85*50000000000000^69 ≤ 21828583343691^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159462959 312500000 21828583343691 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574608791/10000000000 : ℝ)^85 ≤ (14079892514997/50000000000000 : ℝ)^69 := by
    have hnat : (3574608791 : ℕ)^85*50000000000000^69 ≤ 14079892514997^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574608791 10000000000 14079892514997 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1788502889/5000000000 : ℝ)^85 ≤ (1761440516493/6250000000000 : ℝ)^69 := by
    have hnat : (1788502889 : ℕ)^85*6250000000000^69 ≤ 1761440516493^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788502889 5000000000 1761440516493 6250000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(159462959/312500000 : ℝ), (3574608791/10000000000 : ℝ), (1788502889/5000000000 : ℝ)] ![(21828583343691/50000000000000 : ℝ), (14079892514997/50000000000000 : ℝ), (1761440516493/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(159462959/312500000 : ℝ)|^85 ≤ (21828583343691/50000000000000 : ℝ)^69
        have hw : |(159462959/312500000 : ℝ)|=(159462959/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3574608791/10000000000 : ℝ)|^85 ≤ (14079892514997/50000000000000 : ℝ)^69
        have hw : |(3574608791/10000000000 : ℝ)|=(3574608791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1788502889/5000000000 : ℝ)|^85 ≤ (1761440516493/6250000000000 : ℝ)^69
        have hw : |(1788502889/5000000000 : ℝ)|=(1788502889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324087 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((18073/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18073/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((18073/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(18073/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18073/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18073/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-98102887/5000000000 : ℝ)*X 0 0+(5495723527/10000000000 : ℝ)*X 0 1+(5823879729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5823879729/10000000000 : ℝ)*X 1 0+(-98102887/5000000000 : ℝ)*X 1 1+(5495723527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5495723527/10000000000 : ℝ)*X 2 0+(5823879729/10000000000 : ℝ)*X 2 1+(-98102887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1354029249/10000000000 : ℝ)*X 0 0+(42528567/400000000 : ℝ)*X 0 1+(8777487567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4147144929/10000000000 : ℝ)*X 1 0+(-14248767/500000000 : ℝ)*X 1 1+(7043402291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((430662293/2000000000 : ℝ)*X 2 0+(8756569193/10000000000 : ℝ)*X 2 1+(-4308479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2017483669/10000000000 : ℝ)*X 0 0+(7138597467/10000000000 : ℝ)*X 0 1+(169658347/625000000 : ℝ)*X 0 2+(2017483669/10000000000 : ℝ)*X 1 0+(7138597467/10000000000 : ℝ)*X 1 1+(169658347/625000000 : ℝ)*X 1 2+(2017483669/10000000000 : ℝ)*X 2 0+(7138597467/10000000000 : ℝ)*X 2 1+(169658347/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4308479/10000000000 : ℝ)*X 0 0+(430662293/2000000000 : ℝ)*X 0 1+(8756569193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((8777487567/10000000000 : ℝ)*X 1 0+(-1354029249/10000000000 : ℝ)*X 1 1+(42528567/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7043402291/10000000000 : ℝ)*X 2 0+(4147144929/10000000000 : ℝ)*X 2 1+(-14248767/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((169658347/625000000 : ℝ)*X 0 0+(2017483669/10000000000 : ℝ)*X 0 1+(7138597467/10000000000 : ℝ)*X 0 2+(169658347/625000000 : ℝ)*X 1 0+(2017483669/10000000000 : ℝ)*X 1 1+(7138597467/10000000000 : ℝ)*X 1 2+(169658347/625000000 : ℝ)*X 2 0+(2017483669/10000000000 : ℝ)*X 2 1+(7138597467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-14248767/500000000 : ℝ)*X 0 0+(7043402291/10000000000 : ℝ)*X 0 1+(4147144929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8756569193/10000000000 : ℝ)*X 1 0+(-4308479/10000000000 : ℝ)*X 1 1+(430662293/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((42528567/400000000 : ℝ)*X 2 0+(8777487567/10000000000 : ℝ)*X 2 1+(-1354029249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((7138597467/10000000000 : ℝ)*X 0 0+(169658347/625000000 : ℝ)*X 0 1+(2017483669/10000000000 : ℝ)*X 0 2+(7138597467/10000000000 : ℝ)*X 1 0+(169658347/625000000 : ℝ)*X 1 1+(2017483669/10000000000 : ℝ)*X 1 2+(7138597467/10000000000 : ℝ)*X 2 0+(169658347/625000000 : ℝ)*X 2 1+(2017483669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((65221/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65221/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27778537452372261253509/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144765362441/125000000000 : ℝ)*(base7) + (3065983/1000000000000 : ℝ)*(base19) + (18050222997/100000000000 : ℝ)*(base50) + (2254719/1000000000000 : ℝ)*(base53) + (1867426377/50000000000 : ℝ)*(base60) + (695022391347/500000000000 : ℝ)*(major_s0_0) + (695022391347/500000000000 : ℝ)*(major_s0_1) + (695021263987/500000000000 : ℝ)*(major_s0_2) + (4609463/1000000000000 : ℝ)*(sp_s0_0) + (1437804234119/1000000000000 : ℝ)*(sp_s0_7) + (179729615627/125000000000 : ℝ)*(sp_s0_8) + (718921122859/500000000000 : ℝ)*(sp_s0_9) + (929580095417/500000000000 : ℝ)*(sp_s0_13) + (31147417/1000000000000 : ℝ)*(sp_s0_14) + (350518645653/500000000000 : ℝ)*(f.failure) + (718921122859/500000000000 : ℝ)*(f.sum) + (2166613052666833/5000000000000000000000000000 : ℝ)*base62 + (3254005220458697/5000000000000000000000000000 : ℝ)*base65 + (72529529444489/500000000000000000000000000 : ℝ)*base66 + (22883027990169/500000000000000000000000000 : ℝ)*base68 + (1069847436013807/5000000000000000000000000000 : ℝ)*base71 + (528059084765143/5000000000000000000000000000 : ℝ)*base72 + (2107154519234857/5000000000000000000000000000 : ℝ)*base75 + (345599360405511/500000000000000000000000000 : ℝ)*base77 + (969153334289967/5000000000000000000000000000 : ℝ)*base79 + (10137/12500000000000000 : ℝ)*base86 + (10137/12500000000000000 : ℝ)*base88 + (2363/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((65221/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(65221/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27778537452372261253509/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144765362441/125000000000 : ℝ)*(base7) + (3065983/1000000000000 : ℝ)*(base21) + (2254719/1000000000000 : ℝ)*(base33) + (1867426377/50000000000 : ℝ)*(base40) + (18050222997/100000000000 : ℝ)*(base60) + (695021263987/500000000000 : ℝ)*(major_s0_0) + (695022391347/500000000000 : ℝ)*(major_s0_1) + (695022391347/500000000000 : ℝ)*(major_s0_2) + (4609463/1000000000000 : ℝ)*(sp_s0_1) + (718921122859/500000000000 : ℝ)*(sp_s0_14) + (1437804234119/1000000000000 : ℝ)*(sp_s0_15) + (179729615627/125000000000 : ℝ)*(sp_s0_16) + (929580095417/500000000000 : ℝ)*(sp_s0_20) + (31147417/1000000000000 : ℝ)*(sp_s0_22) + (350518645653/500000000000 : ℝ)*(f.failure) + (718921122859/500000000000 : ℝ)*(f.sum) + (969153334289967/5000000000000000000000000000 : ℝ)*base63 + (2107154519234857/5000000000000000000000000000 : ℝ)*base65 + (345599360405511/500000000000000000000000000 : ℝ)*base67 + (72529529444489/500000000000000000000000000 : ℝ)*base68 + (2166613052666833/5000000000000000000000000000 : ℝ)*base70 + (3254005220458697/5000000000000000000000000000 : ℝ)*base73 + (528059084765143/5000000000000000000000000000 : ℝ)*base74 + (22883027990169/500000000000000000000000000 : ℝ)*base76 + (1069847436013807/5000000000000000000000000000 : ℝ)*base79 + (2363/12500000000000000 : ℝ)*base87 + (10137/12500000000000000 : ℝ)*base88 + (10137/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65221/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65221/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27778537452372261253509/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144765362441/125000000000 : ℝ)*(base7) + (3065983/1000000000000 : ℝ)*(base11) + (18050222997/100000000000 : ℝ)*(base40) + (2254719/1000000000000 : ℝ)*(base43) + (1867426377/50000000000 : ℝ)*(base50) + (695022391347/500000000000 : ℝ)*(major_s0_0) + (695021263987/500000000000 : ℝ)*(major_s0_1) + (695022391347/500000000000 : ℝ)*(major_s0_2) + (4609463/1000000000000 : ℝ)*(sp_s0_2) + (31147417/1000000000000 : ℝ)*(sp_s0_9) + (179729615627/125000000000 : ℝ)*(sp_s0_21) + (718921122859/500000000000 : ℝ)*(sp_s0_22) + (1437804234119/1000000000000 : ℝ)*(sp_s0_23) + (929580095417/500000000000 : ℝ)*(sp_s0_27) + (350518645653/500000000000 : ℝ)*(f.failure) + (718921122859/500000000000 : ℝ)*(f.sum) + (1069847436013807/5000000000000000000000000000 : ℝ)*base63 + (528059084765143/5000000000000000000000000000 : ℝ)*base64 + (22883027990169/500000000000000000000000000 : ℝ)*base66 + (345599360405511/500000000000000000000000000 : ℝ)*base69 + (969153334289967/5000000000000000000000000000 : ℝ)*base71 + (2107154519234857/5000000000000000000000000000 : ℝ)*base73 + (3254005220458697/5000000000000000000000000000 : ℝ)*base75 + (72529529444489/500000000000000000000000000 : ℝ)*base76 + (2166613052666833/5000000000000000000000000000 : ℝ)*base78 + (10137/12500000000000000 : ℝ)*base86 + (2363/12500000000000000 : ℝ)*base89 + (10137/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (65221/100000 : ℝ) ^ (21/4 : ℝ) ≤ (10605572813717069509/100000000000000000000 : ℝ) := by
    have hpowers : (65221/100000 : ℝ)^21 ≤ (10605572813717069509/100000000000000000000 : ℝ)^4 := by
      have hnat : (65221 : ℕ)^21*100000000000000000000^4 ≤ 10605572813717069509^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65221 100000 10605572813717069509 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65221/100000 : ℝ)) (X := (10605572813717069509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (110605572813717069509/100000000000000000000 : ℝ) ≤ (10193855614342273/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (110605572813717069509/100000000000000000000 : ℝ)^4 ≤ (10193855614342273/10000000000000000 : ℝ)^21 := by
      have hnat : (110605572813717069509 : ℕ)^4*10000000000000000^21 ≤ 10193855614342273^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110605572813717069509 100000000000000000000 10193855614342273 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10193855614342273/10000000000000000 : ℝ)) (X := (110605572813717069509/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (60605572813717069509/50000000000000000000 : ℝ) ≤ (10373202781090247/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (60605572813717069509/50000000000000000000 : ℝ)^4 ≤ (10373202781090247/10000000000000000 : ℝ)^21 := by
      have hnat : (60605572813717069509 : ℕ)^4*10000000000000000^21 ≤ 10373202781090247^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60605572813717069509 50000000000000000000 10373202781090247 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10373202781090247/10000000000000000 : ℝ)) (X := (60605572813717069509/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14911970334021/501700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(89673583373987/3261050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (65221/100000 : ℝ)) (alpha := (14911970334021/501700000000000 : ℝ)) (beta := (89673583373987/3261050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (65221/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14911970334021/501700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(89673583373987/3261050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (65221/100000 : ℝ) ^ (21/4 : ℝ) ≤ (10605572813717069509/100000000000000000000 : ℝ) := by
    have hpowers : (65221/100000 : ℝ)^21 ≤ (10605572813717069509/100000000000000000000 : ℝ)^4 := by
      have hnat : (65221 : ℕ)^21*100000000000000000000^4 ≤ 10605572813717069509^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65221 100000 10605572813717069509 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65221/100000 : ℝ)) (X := (10605572813717069509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (110605572813717069509/100000000000000000000 : ℝ) ≤ (10193855614342273/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (110605572813717069509/100000000000000000000 : ℝ)^4 ≤ (10193855614342273/10000000000000000 : ℝ)^21 := by
      have hnat : (110605572813717069509 : ℕ)^4*10000000000000000^21 ≤ 10193855614342273^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110605572813717069509 100000000000000000000 10193855614342273 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10193855614342273/10000000000000000 : ℝ)) (X := (110605572813717069509/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60605572813717069509/50000000000000000000 : ℝ) ≤ (10373202781090247/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (60605572813717069509/50000000000000000000 : ℝ)^4 ≤ (10373202781090247/10000000000000000 : ℝ)^21 := by
      have hnat : (60605572813717069509 : ℕ)^4*10000000000000000^21 ≤ 10373202781090247^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60605572813717069509 50000000000000000000 10373202781090247 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10373202781090247/10000000000000000 : ℝ)) (X := (60605572813717069509/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14911970334021/501700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(89673583373987/3261050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (65221/100000 : ℝ)) (alpha := (14911970334021/501700000000000 : ℝ)) (beta := (89673583373987/3261050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (65221/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14911970334021/501700000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(89673583373987/3261050000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65221/100000 : ℝ) ^ (21/4 : ℝ) ≤ (10605572813717069509/100000000000000000000 : ℝ) := by
    have hpowers : (65221/100000 : ℝ)^21 ≤ (10605572813717069509/100000000000000000000 : ℝ)^4 := by
      have hnat : (65221 : ℕ)^21*100000000000000000000^4 ≤ 10605572813717069509^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65221 100000 10605572813717069509 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65221/100000 : ℝ)) (X := (10605572813717069509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110605572813717069509/100000000000000000000 : ℝ) ≤ (10193855614342273/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (110605572813717069509/100000000000000000000 : ℝ)^4 ≤ (10193855614342273/10000000000000000 : ℝ)^21 := by
      have hnat : (110605572813717069509 : ℕ)^4*10000000000000000^21 ≤ 10193855614342273^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110605572813717069509 100000000000000000000 10193855614342273 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10193855614342273/10000000000000000 : ℝ)) (X := (110605572813717069509/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60605572813717069509/50000000000000000000 : ℝ) ≤ (10373202781090247/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (60605572813717069509/50000000000000000000 : ℝ)^4 ≤ (10373202781090247/10000000000000000 : ℝ)^21 := by
      have hnat : (60605572813717069509 : ℕ)^4*10000000000000000^21 ≤ 10373202781090247^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60605572813717069509 50000000000000000000 10373202781090247 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10373202781090247/10000000000000000 : ℝ)) (X := (60605572813717069509/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(14911970334021/501700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(89673583373987/3261050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (65221/100000 : ℝ)) (alpha := (14911970334021/501700000000000 : ℝ)) (beta := (89673583373987/3261050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65221/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(14911970334021/501700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(89673583373987/3261050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-246869709/2500000000 : ℝ)*X 0 0+(5421058187/10000000000 : ℝ)*X 0 1+(2717875179/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2717875299/5000000000 : ℝ)*X 1 0+(-987478717/10000000000 : ℝ)*X 1 1+(5421058027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5421057833/10000000000 : ℝ)*X 2 0+(339734419/625000000 : ℝ)*X 2 1+(-15429357/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-883046747/10000000000 : ℝ)*X 0 0+(899735427/2000000000 : ℝ)*X 0 1+(3194677571/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5670074667/10000000000 : ℝ)*X 1 0+(-41353653/2500000000 : ℝ)*X 1 1+(1132896337/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((171787707/400000000 : ℝ)*X 2 0+(54587457/78125000 : ℝ)*X 2 1+(-28186361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1788502889/5000000000 : ℝ)*X 0 0+(159462959/312500000 : ℝ)*X 0 1+(3574608791/10000000000 : ℝ)*X 0 2+(1788502889/5000000000 : ℝ)*X 1 0+(159462959/312500000 : ℝ)*X 1 1+(3574608791/10000000000 : ℝ)*X 1 2+(1788502889/5000000000 : ℝ)*X 2 0+(159462959/312500000 : ℝ)*X 2 1+(3574608791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-28186361/2500000000 : ℝ)*X 0 0+(171787707/400000000 : ℝ)*X 0 1+(54587457/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3194677571/5000000000 : ℝ)*X 1 0+(-883046747/10000000000 : ℝ)*X 1 1+(899735427/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1132896337/2000000000 : ℝ)*X 2 0+(5670074667/10000000000 : ℝ)*X 2 1+(-41353653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3574608791/10000000000 : ℝ)*X 0 0+(1788502889/5000000000 : ℝ)*X 0 1+(159462959/312500000 : ℝ)*X 0 2+(3574608791/10000000000 : ℝ)*X 1 0+(1788502889/5000000000 : ℝ)*X 1 1+(159462959/312500000 : ℝ)*X 1 2+(3574608791/10000000000 : ℝ)*X 2 0+(1788502889/5000000000 : ℝ)*X 2 1+(159462959/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-41353653/2500000000 : ℝ)*X 0 0+(1132896337/2000000000 : ℝ)*X 0 1+(5670074667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((54587457/78125000 : ℝ)*X 1 0+(-28186361/2500000000 : ℝ)*X 1 1+(171787707/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((899735427/2000000000 : ℝ)*X 2 0+(3194677571/5000000000 : ℝ)*X 2 1+(-883046747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((159462959/312500000 : ℝ)*X 0 0+(3574608791/10000000000 : ℝ)*X 0 1+(1788502889/5000000000 : ℝ)*X 0 2+(159462959/312500000 : ℝ)*X 1 0+(3574608791/10000000000 : ℝ)*X 1 1+(1788502889/5000000000 : ℝ)*X 1 2+(159462959/312500000 : ℝ)*X 2 0+(3574608791/10000000000 : ℝ)*X 2 1+(1788502889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324087_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((18073/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18073/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (87898245934889577/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (4787143/1000000000000 : ℝ)*(base19) + (5124441/500000000000 : ℝ)*(base23) + (389438254057/1000000000000 : ℝ)*(base50) + (356808444141/1000000000000 : ℝ)*(base60) + (916819891399/250000000000 : ℝ)*(major_s1_0) + (916819891399/250000000000 : ℝ)*(major_s1_1) + (916819891399/250000000000 : ℝ)*(major_s1_2) + (4288737/250000000000 : ℝ)*(sp_s1_1) + (5485026700199/1000000000000 : ℝ)*(sp_s1_7) + (5485025692857/1000000000000 : ℝ)*(sp_s1_8) + (5485023778483/1000000000000 : ℝ)*(sp_s1_9) + (1849508566297/1000000000000 : ℝ)*(sp_s1_13) + (20934749/1000000000000 : ℝ)*(sp_s1_14) + (6803791/500000000000 : ℝ)*(sp_s1_23) + (1849508566297/1000000000000 : ℝ)*(f.failure) + (1371261908737/250000000000 : ℝ)*(f.sum) + (1418624437864121/3261050000000000000000000000 : ℝ)*base63 + (328909980555307/815262500000000000000000000 : ℝ)*base64 + (253207342447807/250850000000000000000000000 : ℝ)*base66 + (114982593264307/250850000000000000000000000 : ℝ)*base68 + (103168744055413/1630525000000000000000000000 : ℝ)*base71 + (447500085004097/815262500000000000000000000 : ℝ)*base72 + (2090223562630847/3261050000000000000000000000 : ℝ)*base75 + (168959457089/125425000000000000000000000 : ℝ)*base77 + (1841307629845599/3261050000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (8587/25000000000000000 : ℝ)*base87 + (8587/25000000000000000 : ℝ)*base89 + (8587/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((18073/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(18073/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2204928698289232060263/250850000000000000000000000 : ℝ) := by norm_num
    linear_combination (5124441/500000000000 : ℝ)*(base13) + (4787143/1000000000000 : ℝ)*(base21) + (356808444141/1000000000000 : ℝ)*(base40) + (389438254057/1000000000000 : ℝ)*(base60) + (916819891399/250000000000 : ℝ)*(major_s1_0) + (916819891399/250000000000 : ℝ)*(major_s1_1) + (916819891399/250000000000 : ℝ)*(major_s1_2) + (134023/7812500000 : ℝ)*(sp_s1_2) + (6803791/500000000000 : ℝ)*(sp_s1_7) + (5485023778483/1000000000000 : ℝ)*(sp_s1_14) + (5485026700199/1000000000000 : ℝ)*(sp_s1_15) + (274251284643/50000000000 : ℝ)*(sp_s1_16) + (1849508566297/1000000000000 : ℝ)*(sp_s1_20) + (20934749/1000000000000 : ℝ)*(sp_s1_22) + (1849508566297/1000000000000 : ℝ)*(f.failure) + (5485047634947/1000000000000 : ℝ)*(f.sum) + (1841307629845599/3261050000000000000000000000 : ℝ)*base62 + (2090223562630847/3261050000000000000000000000 : ℝ)*base65 + (168959457089/125425000000000000000000000 : ℝ)*base67 + (253207342447807/250850000000000000000000000 : ℝ)*base68 + (1418624437864121/3261050000000000000000000000 : ℝ)*base71 + (328909980555307/815262500000000000000000000 : ℝ)*base72 + (824985496447457/3261050000000000000000000000 : ℝ)*base75 + (5234501871439/31356250000000000000000000 : ℝ)*base76 + (93533449530407/1630525000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (8587/25000000000000000 : ℝ)*base87 + (8587/25000000000000000 : ℝ)*base89 + (8587/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18073/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18073/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14332023947525435681733/1630525000000000000000000000 : ℝ) := by norm_num
    linear_combination (2393571/500000000000 : ℝ)*(base11) + (5124441/500000000000 : ℝ)*(base15) + (389438254057/1000000000000 : ℝ)*(base40) + (356808444141/1000000000000 : ℝ)*(base50) + (916819891399/250000000000 : ℝ)*(major_s1_0) + (916819891399/250000000000 : ℝ)*(major_s1_1) + (916819891399/250000000000 : ℝ)*(major_s1_2) + (8577473/500000000000 : ℝ)*(sp_s1_0) + (20934749/1000000000000 : ℝ)*(sp_s1_9) + (13607583/1000000000000 : ℝ)*(sp_s1_15) + (274251284643/50000000000 : ℝ)*(sp_s1_21) + (1371255944621/250000000000 : ℝ)*(sp_s1_22) + (5485026700199/1000000000000 : ℝ)*(sp_s1_23) + (1849508566297/1000000000000 : ℝ)*(sp_s1_27) + (1849508566297/1000000000000 : ℝ)*(f.failure) + (1371261908737/250000000000 : ℝ)*(f.sum) + (194922458204653/1630525000000000000000000000 : ℝ)*base63 + (1430019670340293/3261050000000000000000000000 : ℝ)*base64 + (41423204482333/62712500000000000000000000 : ℝ)*base66 + (83803207188763/62712500000000000000000000 : ℝ)*base68 + (189571852174943/407631250000000000000000000 : ℝ)*base70 + (777338299259203/3261050000000000000000000000 : ℝ)*base72 + (328909980555307/815262500000000000000000000 : ℝ)*base74 + (253207342447807/250850000000000000000000000 : ℝ)*base76 + (1418624437864121/3261050000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (8587/25000000000000000 : ℝ)*base87 + (8587/25000000000000000 : ℝ)*base89 + (8587/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_positive87 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  have ho : distinctOrders 87=![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] := by decide
  have hs : ![![true, true, true], ![true, true, true], ![true, true, true]]=(fun (_ _ : Fin 3) => true) := by decide
  have hh := collision_c324087 p hpa (by linarith only [hpb]) X (by simpa only [ho,hs] using hX)
  apply positive_chart_tailratio hX (by decide)
  intro j
  have hn := positive_chart_nonnegative hX j j
  fin_cases j
  · change 0 ≤ pair X 0 0 at hn
    change pair X 0 1 ≤ (2/5:ℝ)*pair X 0 0
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.1,hn]
  · change 0 ≤ pair X 1 1 at hn
    change pair X 1 2 ≤ (2/5:ℝ)*pair X 1 1
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.1,hn]
  · change 0 ≤ pair X 2 2 at hn
    change pair X 2 0 ≤ (2/5:ℝ)*pair X 2 2
    simp only [pair0,pair1,pair2,Pi.add_apply] at hn ⊢
    linarith only [hh.2.2,hn]

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_positive87 p hpa hpb X hX

#print axioms solution
