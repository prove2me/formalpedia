-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b123
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:35:24.592909+00:00
-- url     : https://prove2.me/submissions/47970871-c225-40bd-93c9-7bf1b6af9e98

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
theorem collision_support_c201308_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (12347/5000000000 : ℝ)*x 0 + (-4999999803/5000000000 : ℝ)*x 1 + (899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12347/5000000000 : ℝ)^17 ≤ (4647667/100000000000000 : ℝ)^13 := by
    have hnat : (12347 : ℕ)^17*100000000000000^13 ≤ 4647667^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12347 5000000000 4647667 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999999803/5000000000 : ℝ)^17 ≤ (99999994847693/100000000000000 : ℝ)^13 := by
    have hnat : (4999999803 : ℕ)^17*100000000000000^13 ≤ 99999994847693^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999803 5000000000 99999994847693 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899/2000000000 : ℝ)^17 ≤ (500869/100000000000000 : ℝ)^13 := by
    have hnat : (899 : ℕ)^17*100000000000000^13 ≤ 500869^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899 2000000000 500869 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12347/5000000000 : ℝ), (-4999999803/5000000000 : ℝ), (899/2000000000 : ℝ)] ![(4647667/100000000000000 : ℝ), (99999994847693/100000000000000 : ℝ), (500869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12347/5000000000 : ℝ)|^17 ≤ (4647667/100000000000000 : ℝ)^13
        have hw : |(12347/5000000000 : ℝ)|=(12347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4999999803/5000000000 : ℝ)|^17 ≤ (99999994847693/100000000000000 : ℝ)^13
        have hw : |(-4999999803/5000000000 : ℝ)|=(4999999803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899/2000000000 : ℝ)|^17 ≤ (500869/100000000000000 : ℝ)^13
        have hw : |(899/2000000000 : ℝ)|=(899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (225956363/250000000 : ℝ)*x 0 + (-100879851/5000000000 : ℝ)*x 1 + (1948394021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225956363/250000000 : ℝ)^17 ≤ (87613721137621/100000000000000 : ℝ)^13 := by
    have hnat : (225956363 : ℕ)^17*100000000000000^13 ≤ 87613721137621^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225956363 250000000 87613721137621 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100879851/5000000000 : ℝ)^17 ≤ (121415747123/20000000000000 : ℝ)^13 := by
    have hnat : (100879851 : ℕ)^17*20000000000000^13 ≤ 121415747123^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100879851 5000000000 121415747123 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948394021/10000000000 : ℝ)^17 ≤ (11779200113233/100000000000000 : ℝ)^13 := by
    have hnat : (1948394021 : ℕ)^17*100000000000000^13 ≤ 11779200113233^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948394021 10000000000 11779200113233 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225956363/250000000 : ℝ), (-100879851/5000000000 : ℝ), (1948394021/10000000000 : ℝ)] ![(87613721137621/100000000000000 : ℝ), (121415747123/20000000000000 : ℝ), (11779200113233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225956363/250000000 : ℝ)|^17 ≤ (87613721137621/100000000000000 : ℝ)^13
        have hw : |(225956363/250000000 : ℝ)|=(225956363/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100879851/5000000000 : ℝ)|^17 ≤ (121415747123/20000000000000 : ℝ)^13
        have hw : |(-100879851/5000000000 : ℝ)|=(100879851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1948394021/10000000000 : ℝ)|^17 ≤ (11779200113233/100000000000000 : ℝ)^13
        have hw : |(1948394021/10000000000 : ℝ)|=(1948394021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (171217/10000000000 : ℝ)*x 0 + (-9999916347/10000000000 : ℝ)*x 1 + (-1541829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171217/10000000000 : ℝ)^17 ≤ (3654483/6250000000000 : ℝ)^13 := by
    have hnat : (171217 : ℕ)^17*6250000000000^13 ≤ 3654483^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171217 10000000000 3654483 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999916347/10000000000 : ℝ)^17 ≤ (49999453038781/50000000000000 : ℝ)^13 := by
    have hnat : (9999916347 : ℕ)^17*50000000000000^13 ≤ 49999453038781^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999916347 10000000000 49999453038781 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1541829/10000000000 : ℝ)^17 ≤ (517719209/50000000000000 : ℝ)^13 := by
    have hnat : (1541829 : ℕ)^17*50000000000000^13 ≤ 517719209^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541829 10000000000 517719209 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171217/10000000000 : ℝ), (-9999916347/10000000000 : ℝ), (-1541829/10000000000 : ℝ)] ![(3654483/6250000000000 : ℝ), (49999453038781/50000000000000 : ℝ), (517719209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171217/10000000000 : ℝ)|^17 ≤ (3654483/6250000000000 : ℝ)^13
        have hw : |(171217/10000000000 : ℝ)|=(171217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9999916347/10000000000 : ℝ)|^17 ≤ (49999453038781/50000000000000 : ℝ)^13
        have hw : |(-9999916347/10000000000 : ℝ)|=(9999916347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1541829/10000000000 : ℝ)|^17 ≤ (517719209/50000000000000 : ℝ)^13
        have hw : |(-1541829/10000000000 : ℝ)|=(1541829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-31205431/10000000000 : ℝ)*x 0 + (-3884981431/5000000000 : ℝ)*x 1 + (1891560877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31205431/10000000000 : ℝ)^17 ≤ (52871799079/100000000000000 : ℝ)^13 := by
    have hnat : (31205431 : ℕ)^17*100000000000000^13 ≤ 52871799079^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31205431 10000000000 52871799079 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3884981431/5000000000 : ℝ)^17 ≤ (71895497737761/100000000000000 : ℝ)^13 := by
    have hnat : (3884981431 : ℕ)^17*100000000000000^13 ≤ 71895497737761^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884981431 5000000000 71895497737761 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1891560877/5000000000 : ℝ)^17 ≤ (5610326090847/20000000000000 : ℝ)^13 := by
    have hnat : (1891560877 : ℕ)^17*20000000000000^13 ≤ 5610326090847^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891560877 5000000000 5610326090847 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31205431/10000000000 : ℝ), (-3884981431/5000000000 : ℝ), (1891560877/5000000000 : ℝ)] ![(52871799079/100000000000000 : ℝ), (71895497737761/100000000000000 : ℝ), (5610326090847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31205431/10000000000 : ℝ)|^17 ≤ (52871799079/100000000000000 : ℝ)^13
        have hw : |(-31205431/10000000000 : ℝ)|=(31205431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3884981431/5000000000 : ℝ)|^17 ≤ (71895497737761/100000000000000 : ℝ)^13
        have hw : |(-3884981431/5000000000 : ℝ)|=(3884981431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1891560877/5000000000 : ℝ)|^17 ≤ (5610326090847/20000000000000 : ℝ)^13
        have hw : |(1891560877/5000000000 : ℝ)|=(1891560877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8849729999/10000000000 : ℝ)*x 0 + (128146397/5000000000 : ℝ)*x 1 + (1108005977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8849729999/10000000000 : ℝ)^17 ≤ (42615815224351/50000000000000 : ℝ)^13 := by
    have hnat : (8849729999 : ℕ)^17*50000000000000^13 ≤ 42615815224351^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8849729999 10000000000 42615815224351 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128146397/5000000000 : ℝ)^17 ≤ (415037013521/50000000000000 : ℝ)^13 := by
    have hnat : (128146397 : ℕ)^17*50000000000000^13 ≤ 415037013521^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128146397 5000000000 415037013521 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108005977/5000000000 : ℝ)^17 ≤ (6969147751553/50000000000000 : ℝ)^13 := by
    have hnat : (1108005977 : ℕ)^17*50000000000000^13 ≤ 6969147751553^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108005977 5000000000 6969147751553 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8849729999/10000000000 : ℝ), (128146397/5000000000 : ℝ), (1108005977/5000000000 : ℝ)] ![(42615815224351/50000000000000 : ℝ), (415037013521/50000000000000 : ℝ), (6969147751553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8849729999/10000000000 : ℝ)|^17 ≤ (42615815224351/50000000000000 : ℝ)^13
        have hw : |(8849729999/10000000000 : ℝ)|=(8849729999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128146397/5000000000 : ℝ)|^17 ≤ (415037013521/50000000000000 : ℝ)^13
        have hw : |(128146397/5000000000 : ℝ)|=(128146397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108005977/5000000000 : ℝ)|^17 ≤ (6969147751553/50000000000000 : ℝ)^13
        have hw : |(1108005977/5000000000 : ℝ)|=(1108005977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8587015863/10000000000 : ℝ)*x 0 + (-156018511/10000000000 : ℝ)*x 1 + (1325987719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8587015863/10000000000 : ℝ)^17 ≤ (20484532069129/25000000000000 : ℝ)^13 := by
    have hnat : (8587015863 : ℕ)^17*25000000000000^13 ≤ 20484532069129^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8587015863 10000000000 20484532069129 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156018511/10000000000 : ℝ)^17 ≤ (86748169211/20000000000000 : ℝ)^13 := by
    have hnat : (156018511 : ℕ)^17*20000000000000^13 ≤ 86748169211^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156018511 10000000000 86748169211 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1325987719/5000000000 : ℝ)^17 ≤ (881406543149/5000000000000 : ℝ)^13 := by
    have hnat : (1325987719 : ℕ)^17*5000000000000^13 ≤ 881406543149^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325987719 5000000000 881406543149 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8587015863/10000000000 : ℝ), (-156018511/10000000000 : ℝ), (1325987719/5000000000 : ℝ)] ![(20484532069129/25000000000000 : ℝ), (86748169211/20000000000000 : ℝ), (881406543149/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8587015863/10000000000 : ℝ)|^17 ≤ (20484532069129/25000000000000 : ℝ)^13
        have hw : |(8587015863/10000000000 : ℝ)|=(8587015863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156018511/10000000000 : ℝ)|^17 ≤ (86748169211/20000000000000 : ℝ)^13
        have hw : |(-156018511/10000000000 : ℝ)|=(156018511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1325987719/5000000000 : ℝ)|^17 ≤ (881406543149/5000000000000 : ℝ)^13
        have hw : |(1325987719/5000000000 : ℝ)|=(1325987719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-137863/10000000000 : ℝ)*x 0 + (-9734015571/10000000000 : ℝ)*x 1 + (382090543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137863/10000000000 : ℝ)^17 ≤ (11011163/25000000000000 : ℝ)^13 := by
    have hnat : (137863 : ℕ)^17*25000000000000^13 ≤ 11011163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137863 10000000000 11011163 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9734015571/10000000000 : ℝ)^17 ≤ (4826803185671/5000000000000 : ℝ)^13 := by
    have hnat : (9734015571 : ℕ)^17*5000000000000^13 ≤ 4826803185671^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9734015571 10000000000 4826803185671 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382090543/5000000000 : ℝ)^17 ≤ (1731946116193/50000000000000 : ℝ)^13 := by
    have hnat : (382090543 : ℕ)^17*50000000000000^13 ≤ 1731946116193^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382090543 5000000000 1731946116193 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137863/10000000000 : ℝ), (-9734015571/10000000000 : ℝ), (382090543/5000000000 : ℝ)] ![(11011163/25000000000000 : ℝ), (4826803185671/5000000000000 : ℝ), (1731946116193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137863/10000000000 : ℝ)|^17 ≤ (11011163/25000000000000 : ℝ)^13
        have hw : |(-137863/10000000000 : ℝ)|=(137863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9734015571/10000000000 : ℝ)|^17 ≤ (4826803185671/5000000000000 : ℝ)^13
        have hw : |(-9734015571/10000000000 : ℝ)|=(9734015571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(382090543/5000000000 : ℝ)|^17 ≤ (1731946116193/50000000000000 : ℝ)^13
        have hw : |(382090543/5000000000 : ℝ)|=(382090543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (14649629/5000000000 : ℝ)*x 0 + (-2204838049/5000000000 : ℝ)*x 1 + (-7250451523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14649629/5000000000 : ℝ)^17 ≤ (48688667649/100000000000000 : ℝ)^13 := by
    have hnat : (14649629 : ℕ)^17*100000000000000^13 ≤ 48688667649^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14649629 5000000000 48688667649 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204838049/5000000000 : ℝ)^17 ≤ (17138127480283/50000000000000 : ℝ)^13 := by
    have hnat : (2204838049 : ℕ)^17*50000000000000^13 ≤ 17138127480283^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204838049 5000000000 17138127480283 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7250451523/10000000000 : ℝ)^17 ≤ (65675056358603/100000000000000 : ℝ)^13 := by
    have hnat : (7250451523 : ℕ)^17*100000000000000^13 ≤ 65675056358603^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7250451523 10000000000 65675056358603 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14649629/5000000000 : ℝ), (-2204838049/5000000000 : ℝ), (-7250451523/10000000000 : ℝ)] ![(48688667649/100000000000000 : ℝ), (17138127480283/50000000000000 : ℝ), (65675056358603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14649629/5000000000 : ℝ)|^17 ≤ (48688667649/100000000000000 : ℝ)^13
        have hw : |(14649629/5000000000 : ℝ)|=(14649629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2204838049/5000000000 : ℝ)|^17 ≤ (17138127480283/50000000000000 : ℝ)^13
        have hw : |(-2204838049/5000000000 : ℝ)|=(2204838049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7250451523/10000000000 : ℝ)|^17 ≤ (65675056358603/100000000000000 : ℝ)^13
        have hw : |(-7250451523/10000000000 : ℝ)|=(7250451523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9312953103/10000000000 : ℝ)*x 0 + (33441831/2000000000 : ℝ)*x 1 + (376570833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9312953103/10000000000 : ℝ)^17 ≤ (45556028504859/50000000000000 : ℝ)^13 := by
    have hnat : (9312953103 : ℕ)^17*50000000000000^13 ≤ 45556028504859^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9312953103 10000000000 45556028504859 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33441831/2000000000 : ℝ)^17 ≤ (237432869801/50000000000000 : ℝ)^13 := by
    have hnat : (33441831 : ℕ)^17*50000000000000^13 ≤ 237432869801^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33441831 2000000000 237432869801 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376570833/2500000000 : ℝ)^17 ≤ (2103269312283/25000000000000 : ℝ)^13 := by
    have hnat : (376570833 : ℕ)^17*25000000000000^13 ≤ 2103269312283^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376570833 2500000000 2103269312283 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9312953103/10000000000 : ℝ), (33441831/2000000000 : ℝ), (376570833/2500000000 : ℝ)] ![(45556028504859/50000000000000 : ℝ), (237432869801/50000000000000 : ℝ), (2103269312283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9312953103/10000000000 : ℝ)|^17 ≤ (45556028504859/50000000000000 : ℝ)^13
        have hw : |(9312953103/10000000000 : ℝ)|=(9312953103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33441831/2000000000 : ℝ)|^17 ≤ (237432869801/50000000000000 : ℝ)^13
        have hw : |(33441831/2000000000 : ℝ)|=(33441831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376570833/2500000000 : ℝ)|^17 ≤ (2103269312283/25000000000000 : ℝ)^13
        have hw : |(376570833/2500000000 : ℝ)|=(376570833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1666411491/2000000000 : ℝ)*x 0 + (-135475159/5000000000 : ℝ)*x 1 + (2958187881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1666411491/2000000000 : ℝ)^17 ≤ (19692839597029/25000000000000 : ℝ)^13 := by
    have hnat : (1666411491 : ℕ)^17*25000000000000^13 ≤ 19692839597029^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666411491 2000000000 19692839597029 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135475159/5000000000 : ℝ)^17 ≤ (223173116597/25000000000000 : ℝ)^13 := by
    have hnat : (135475159 : ℕ)^17*25000000000000^13 ≤ 223173116597^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135475159 5000000000 223173116597 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2958187881/10000000000 : ℝ)^17 ≤ (20335949134429/100000000000000 : ℝ)^13 := by
    have hnat : (2958187881 : ℕ)^17*100000000000000^13 ≤ 20335949134429^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958187881 10000000000 20335949134429 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1666411491/2000000000 : ℝ), (-135475159/5000000000 : ℝ), (2958187881/10000000000 : ℝ)] ![(19692839597029/25000000000000 : ℝ), (223173116597/25000000000000 : ℝ), (20335949134429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1666411491/2000000000 : ℝ)|^17 ≤ (19692839597029/25000000000000 : ℝ)^13
        have hw : |(1666411491/2000000000 : ℝ)|=(1666411491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135475159/5000000000 : ℝ)|^17 ≤ (223173116597/25000000000000 : ℝ)^13
        have hw : |(-135475159/5000000000 : ℝ)|=(135475159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2958187881/10000000000 : ℝ)|^17 ≤ (20335949134429/100000000000000 : ℝ)^13
        have hw : |(2958187881/10000000000 : ℝ)|=(2958187881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (16961/2000000000 : ℝ)*x 0 + (-1996236861/2000000000 : ℝ)*x 1 + (101105413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16961/2000000000 : ℝ)^17 ≤ (23331129/100000000000000 : ℝ)^13 := by
    have hnat : (16961 : ℕ)^17*100000000000000^13 ≤ 23331129^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16961 2000000000 23331129 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996236861/2000000000 : ℝ)^17 ≤ (24938504964961/25000000000000 : ℝ)^13 := by
    have hnat : (1996236861 : ℕ)^17*25000000000000^13 ≤ 24938504964961^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996236861 2000000000 24938504964961 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101105413/10000000000 : ℝ)^17 ≤ (24595680373/10000000000000 : ℝ)^13 := by
    have hnat : (101105413 : ℕ)^17*10000000000000^13 ≤ 24595680373^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101105413 10000000000 24595680373 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16961/2000000000 : ℝ), (-1996236861/2000000000 : ℝ), (101105413/10000000000 : ℝ)] ![(23331129/100000000000000 : ℝ), (24938504964961/25000000000000 : ℝ), (24595680373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16961/2000000000 : ℝ)|^17 ≤ (23331129/100000000000000 : ℝ)^13
        have hw : |(16961/2000000000 : ℝ)|=(16961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996236861/2000000000 : ℝ)|^17 ≤ (24938504964961/25000000000000 : ℝ)^13
        have hw : |(-1996236861/2000000000 : ℝ)|=(1996236861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101105413/10000000000 : ℝ)|^17 ≤ (24595680373/10000000000000 : ℝ)^13
        have hw : |(101105413/10000000000 : ℝ)|=(101105413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2280159/1250000000 : ℝ)*x 0 + (-456297361/2500000000 : ℝ)*x 1 + (4579953497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2280159/1250000000 : ℝ)^17 ≤ (3275011741/12500000000000 : ℝ)^13 := by
    have hnat : (2280159 : ℕ)^17*12500000000000^13 ≤ 3275011741^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280159 1250000000 3275011741 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456297361/2500000000 : ℝ)^17 ≤ (2703697472163/25000000000000 : ℝ)^13 := by
    have hnat : (456297361 : ℕ)^17*25000000000000^13 ≤ 2703697472163^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456297361 2500000000 2703697472163 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4579953497/5000000000 : ℝ)^17 ≤ (89159010011363/100000000000000 : ℝ)^13 := by
    have hnat : (4579953497 : ℕ)^17*100000000000000^13 ≤ 89159010011363^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579953497 5000000000 89159010011363 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2280159/1250000000 : ℝ), (-456297361/2500000000 : ℝ), (4579953497/5000000000 : ℝ)] ![(3275011741/12500000000000 : ℝ), (2703697472163/25000000000000 : ℝ), (89159010011363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2280159/1250000000 : ℝ)|^17 ≤ (3275011741/12500000000000 : ℝ)^13
        have hw : |(-2280159/1250000000 : ℝ)|=(2280159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456297361/2500000000 : ℝ)|^17 ≤ (2703697472163/25000000000000 : ℝ)^13
        have hw : |(-456297361/2500000000 : ℝ)|=(456297361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4579953497/5000000000 : ℝ)|^17 ≤ (89159010011363/100000000000000 : ℝ)^13
        have hw : |(4579953497/5000000000 : ℝ)|=(4579953497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1940262673/2000000000 : ℝ)*x 0 + (205853483/10000000000 : ℝ)*x 1 + (730325059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940262673/2000000000 : ℝ)^17 ≤ (961121714721/1000000000000 : ℝ)^13 := by
    have hnat : (1940262673 : ℕ)^17*1000000000000^13 ≤ 961121714721^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940262673 2000000000 961121714721 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205853483/10000000000 : ℝ)^17 ≤ (62323675313/10000000000000 : ℝ)^13 := by
    have hnat : (205853483 : ℕ)^17*10000000000000^13 ≤ 62323675313^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205853483 10000000000 62323675313 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730325059/10000000000 : ℝ)^17 ≤ (1632295880121/50000000000000 : ℝ)^13 := by
    have hnat : (730325059 : ℕ)^17*50000000000000^13 ≤ 1632295880121^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730325059 10000000000 1632295880121 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1940262673/2000000000 : ℝ), (205853483/10000000000 : ℝ), (730325059/10000000000 : ℝ)] ![(961121714721/1000000000000 : ℝ), (62323675313/10000000000000 : ℝ), (1632295880121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1940262673/2000000000 : ℝ)|^17 ≤ (961121714721/1000000000000 : ℝ)^13
        have hw : |(1940262673/2000000000 : ℝ)|=(1940262673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205853483/10000000000 : ℝ)|^17 ≤ (62323675313/10000000000000 : ℝ)^13
        have hw : |(205853483/10000000000 : ℝ)|=(205853483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(730325059/10000000000 : ℝ)|^17 ≤ (1632295880121/50000000000000 : ℝ)^13
        have hw : |(730325059/10000000000 : ℝ)|=(730325059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s0_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (344895259/400000000 : ℝ)*x 0 + (-19800493/1000000000 : ℝ)*x 1 + (2582648561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344895259/400000000 : ℝ)^17 ≤ (41189852080959/50000000000000 : ℝ)^13 := by
    have hnat : (344895259 : ℕ)^17*50000000000000^13 ≤ 41189852080959^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344895259 400000000 41189852080959 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19800493/1000000000 : ℝ)^17 ≤ (296173581261/50000000000000 : ℝ)^13 := by
    have hnat : (19800493 : ℕ)^17*50000000000000^13 ≤ 296173581261^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19800493 1000000000 296173581261 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582648561/10000000000 : ℝ)^17 ≤ (17027948656927/100000000000000 : ℝ)^13 := by
    have hnat : (2582648561 : ℕ)^17*100000000000000^13 ≤ 17027948656927^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582648561 10000000000 17027948656927 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344895259/400000000 : ℝ), (-19800493/1000000000 : ℝ), (2582648561/10000000000 : ℝ)] ![(41189852080959/50000000000000 : ℝ), (296173581261/50000000000000 : ℝ), (17027948656927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344895259/400000000 : ℝ)|^17 ≤ (41189852080959/50000000000000 : ℝ)^13
        have hw : |(344895259/400000000 : ℝ)|=(344895259/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19800493/1000000000 : ℝ)|^17 ≤ (296173581261/50000000000000 : ℝ)^13
        have hw : |(-19800493/1000000000 : ℝ)|=(19800493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582648561/10000000000 : ℝ)|^17 ≤ (17027948656927/100000000000000 : ℝ)^13
        have hw : |(2582648561/10000000000 : ℝ)|=(2582648561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-108459/10000000000 : ℝ)*x 0 + (-31236109/31250000 : ℝ)*x 1 + (1047979/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108459/10000000000 : ℝ)^17 ≤ (32185111/100000000000000 : ℝ)^13 := by
    have hnat : (108459 : ℕ)^17*100000000000000^13 ≤ 32185111^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108459 10000000000 32185111 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31236109/31250000 : ℝ)^17 ≤ (99941875483303/100000000000000 : ℝ)^13 := by
    have hnat : (31236109 : ℕ)^17*100000000000000^13 ≤ 99941875483303^13*31250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31236109 31250000 99941875483303 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047979/312500000 : ℝ)^17 ≤ (14523080309/25000000000000 : ℝ)^13 := by
    have hnat : (1047979 : ℕ)^17*25000000000000^13 ≤ 14523080309^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047979 312500000 14523080309 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108459/10000000000 : ℝ), (-31236109/31250000 : ℝ), (1047979/312500000 : ℝ)] ![(32185111/100000000000000 : ℝ), (99941875483303/100000000000000 : ℝ), (14523080309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108459/10000000000 : ℝ)|^17 ≤ (32185111/100000000000000 : ℝ)^13
        have hw : |(-108459/10000000000 : ℝ)|=(108459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31236109/31250000 : ℝ)|^17 ≤ (99941875483303/100000000000000 : ℝ)^13
        have hw : |(-31236109/31250000 : ℝ)|=(31236109/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047979/312500000 : ℝ)|^17 ≤ (14523080309/25000000000000 : ℝ)^13
        have hw : |(1047979/312500000 : ℝ)|=(1047979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (30451047/2000000000 : ℝ)*x 0 + (-4799399081/5000000000 : ℝ)*x 1 + (-979716283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30451047/2000000000 : ℝ)^17 ≤ (420110649307/100000000000000 : ℝ)^13 := by
    have hnat : (30451047 : ℕ)^17*100000000000000^13 ≤ 420110649307^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30451047 2000000000 420110649307 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4799399081/5000000000 : ℝ)^17 ≤ (47393101259201/50000000000000 : ℝ)^13 := by
    have hnat : (4799399081 : ℕ)^17*50000000000000^13 ≤ 47393101259201^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799399081 5000000000 47393101259201 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979716283/10000000000 : ℝ)^17 ≤ (4793686818359/100000000000000 : ℝ)^13 := by
    have hnat : (979716283 : ℕ)^17*100000000000000^13 ≤ 4793686818359^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979716283 10000000000 4793686818359 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30451047/2000000000 : ℝ), (-4799399081/5000000000 : ℝ), (-979716283/10000000000 : ℝ)] ![(420110649307/100000000000000 : ℝ), (47393101259201/50000000000000 : ℝ), (4793686818359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30451047/2000000000 : ℝ)|^17 ≤ (420110649307/100000000000000 : ℝ)^13
        have hw : |(30451047/2000000000 : ℝ)|=(30451047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4799399081/5000000000 : ℝ)|^17 ≤ (47393101259201/50000000000000 : ℝ)^13
        have hw : |(-4799399081/5000000000 : ℝ)|=(4799399081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979716283/10000000000 : ℝ)|^17 ≤ (4793686818359/100000000000000 : ℝ)^13
        have hw : |(-979716283/10000000000 : ℝ)|=(979716283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9695160043/10000000000 : ℝ)*x 0 + (3162641/250000000 : ℝ)*x 1 + (793353809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9695160043/10000000000 : ℝ)^17 ≤ (3841298401097/4000000000000 : ℝ)^13 := by
    have hnat : (9695160043 : ℕ)^17*4000000000000^13 ≤ 3841298401097^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9695160043 10000000000 3841298401097 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3162641/250000000 : ℝ)^17 ≤ (329718791829/100000000000000 : ℝ)^13 := by
    have hnat : (3162641 : ℕ)^17*100000000000000^13 ≤ 329718791829^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162641 250000000 329718791829 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793353809/10000000000 : ℝ)^17 ≤ (3637821165237/100000000000000 : ℝ)^13 := by
    have hnat : (793353809 : ℕ)^17*100000000000000^13 ≤ 3637821165237^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793353809 10000000000 3637821165237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9695160043/10000000000 : ℝ), (3162641/250000000 : ℝ), (793353809/10000000000 : ℝ)] ![(3841298401097/4000000000000 : ℝ), (329718791829/100000000000000 : ℝ), (3637821165237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9695160043/10000000000 : ℝ)|^17 ≤ (3841298401097/4000000000000 : ℝ)^13
        have hw : |(9695160043/10000000000 : ℝ)|=(9695160043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3162641/250000000 : ℝ)|^17 ≤ (329718791829/100000000000000 : ℝ)^13
        have hw : |(3162641/250000000 : ℝ)|=(3162641/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793353809/10000000000 : ℝ)|^17 ≤ (3637821165237/100000000000000 : ℝ)^13
        have hw : |(793353809/10000000000 : ℝ)|=(793353809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201308_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9433232591/10000000000 : ℝ)*x 0 + (-159436603/5000000000 : ℝ)*x 1 + (1198812087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9433232591/10000000000 : ℝ)^17 ≤ (46326958777723/50000000000000 : ℝ)^13 := by
    have hnat : (9433232591 : ℕ)^17*50000000000000^13 ≤ 46326958777723^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9433232591 10000000000 46326958777723 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159436603/5000000000 : ℝ)^17 ≤ (69035555459/6250000000000 : ℝ)^13 := by
    have hnat : (159436603 : ℕ)^17*6250000000000^13 ≤ 69035555459^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159436603 5000000000 69035555459 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198812087/10000000000 : ℝ)^17 ≤ (312075677069/5000000000000 : ℝ)^13 := by
    have hnat : (1198812087 : ℕ)^17*5000000000000^13 ≤ 312075677069^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198812087 10000000000 312075677069 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9433232591/10000000000 : ℝ), (-159436603/5000000000 : ℝ), (1198812087/10000000000 : ℝ)] ![(46326958777723/50000000000000 : ℝ), (69035555459/6250000000000 : ℝ), (312075677069/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9433232591/10000000000 : ℝ)|^17 ≤ (46326958777723/50000000000000 : ℝ)^13
        have hw : |(9433232591/10000000000 : ℝ)|=(9433232591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159436603/5000000000 : ℝ)|^17 ≤ (69035555459/6250000000000 : ℝ)^13
        have hw : |(-159436603/5000000000 : ℝ)|=(159436603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198812087/10000000000 : ℝ)|^17 ≤ (312075677069/5000000000000 : ℝ)^13
        have hw : |(1198812087/10000000000 : ℝ)|=(1198812087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c201308 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) ∧ ((-1 : ℝ)*(X 0 1+X 2 1)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 1) ∧ ((-1 : ℝ)*pair X 1 1) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) ∧ ((1 : ℝ)*(X 0 2+X 1 2)) ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) ∧ ((1 : ℝ)*pair X 2 2) ≤ ((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 1+X 1 1))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 1 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 1)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((12347/5000000000 : ℝ)*X 0 0+(-4999999803/5000000000 : ℝ)*X 0 1+(899/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((225956363/250000000 : ℝ)*X 0 0+(-100879851/5000000000 : ℝ)*X 0 1+(1948394021/10000000000 : ℝ)*X 0 2+(225956363/250000000 : ℝ)*X 1 0+(-100879851/5000000000 : ℝ)*X 1 1+(1948394021/10000000000 : ℝ)*X 1 2+(225956363/250000000 : ℝ)*X 2 0+(-100879851/5000000000 : ℝ)*X 2 1+(1948394021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((171217/10000000000 : ℝ)*X 0 0+(-9999916347/10000000000 : ℝ)*X 0 1+(-1541829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((-31205431/10000000000 : ℝ)*X 1 0+(-3884981431/5000000000 : ℝ)*X 1 1+(1891560877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((8849729999/10000000000 : ℝ)*X 2 0+(128146397/5000000000 : ℝ)*X 2 1+(1108005977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((8587015863/10000000000 : ℝ)*X 0 0+(-156018511/10000000000 : ℝ)*X 0 1+(1325987719/5000000000 : ℝ)*X 0 2+(8587015863/10000000000 : ℝ)*X 1 0+(-156018511/10000000000 : ℝ)*X 1 1+(1325987719/5000000000 : ℝ)*X 1 2+(8587015863/10000000000 : ℝ)*X 2 0+(-156018511/10000000000 : ℝ)*X 2 1+(1325987719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-137863/10000000000 : ℝ)*X 0 0+(-9734015571/10000000000 : ℝ)*X 0 1+(382090543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((14649629/5000000000 : ℝ)*X 1 0+(-2204838049/5000000000 : ℝ)*X 1 1+(-7250451523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((9312953103/10000000000 : ℝ)*X 2 0+(33441831/2000000000 : ℝ)*X 2 1+(376570833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1666411491/2000000000 : ℝ)*X 0 0+(-135475159/5000000000 : ℝ)*X 0 1+(2958187881/10000000000 : ℝ)*X 0 2+(1666411491/2000000000 : ℝ)*X 1 0+(-135475159/5000000000 : ℝ)*X 1 1+(2958187881/10000000000 : ℝ)*X 1 2+(1666411491/2000000000 : ℝ)*X 2 0+(-135475159/5000000000 : ℝ)*X 2 1+(2958187881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((16961/2000000000 : ℝ)*X 0 0+(-1996236861/2000000000 : ℝ)*X 0 1+(101105413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((-2280159/1250000000 : ℝ)*X 1 0+(-456297361/2500000000 : ℝ)*X 1 1+(4579953497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1940262673/2000000000 : ℝ)*X 2 0+(205853483/10000000000 : ℝ)*X 2 1+(730325059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((344895259/400000000 : ℝ)*X 0 0+(-19800493/1000000000 : ℝ)*X 0 1+(2582648561/10000000000 : ℝ)*X 0 2+(344895259/400000000 : ℝ)*X 1 0+(-19800493/1000000000 : ℝ)*X 1 1+(2582648561/10000000000 : ℝ)*X 1 2+(344895259/400000000 : ℝ)*X 2 0+(-19800493/1000000000 : ℝ)*X 2 1+(2582648561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((37281/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(37281/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9493349092714266550617/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (678434865923/250000000000 : ℝ)*(base7) + (3242111507/40000000000 : ℝ)*(base33) + (204312916469/250000000000 : ℝ)*(base44) + (381219/500000000000 : ℝ)*(base49) + (3602779557751/1000000000000 : ℝ)*(base53) + (132528390839/1000000000000 : ℝ)*(base59) + (1694889883597/250000000000 : ℝ)*(major_s0_0) + (3021680328093/500000000000 : ℝ)*(major_s0_1) + (407229095539/125000000000 : ℝ)*(major_s0_2) + (28581831027/1000000000000 : ℝ)*(sp_s0_0) + (3867544470359/1000000000000 : ℝ)*(sp_s0_7) + (599564369567/200000000000 : ℝ)*(sp_s0_8) + (3708926535731/500000000000 : ℝ)*(sp_s0_9) + (6419809387867/1000000000000 : ℝ)*(sp_s0_13) + (4523321590051/1000000000000 : ℝ)*(f.failure) + (7498905859137/1000000000000 : ℝ)*(f.sum) + (691542488893/12500000000000000000000000 : ℝ)*base62 + (19847293190591/50000000000000000000000000 : ℝ)*base64 + (27882391626043/1000000000000000000000000000 : ℝ)*base66 + (4588994418607/12500000000000000000000000 : ℝ)*base69 + (2499632471061/25000000000000000000000000 : ℝ)*base70 + (1310637463809/20000000000000000000000000 : ℝ)*base72 + (1800922759/10000000000000000000000 : ℝ)*base74 + (8112500982713/50000000000000000000000000 : ℝ)*base76 + (57446480007909/1000000000000000000000000000 : ℝ)*base78 + (10591/12500000000000000 : ℝ)*base86 + (1909/12500000000000000 : ℝ)*base89 + (10591/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((16793/20000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(16793/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15330507496681235220249/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3533996346779/1000000000000 : ℝ)*(base7) + (224190730449/200000000000 : ℝ)*(base33) + (178967/250000000000 : ℝ)*(base39) + (285163001059/1000000000000 : ℝ)*(base44) + (7338861694563/1000000000000 : ℝ)*(base53) + (13832555093/200000000000 : ℝ)*(base59) + (1605023176583/200000000000 : ℝ)*(major_s0_0) + (88609065341/10000000000 : ℝ)*(major_s0_1) + (451801960149/250000000000 : ℝ)*(major_s0_2) + (2710579704769/1000000000000 : ℝ)*(sp_s0_14) + (260892610293/200000000000 : ℝ)*(sp_s0_15) + (4464241396109/500000000000 : ℝ)*(sp_s0_16) + (9278996813703/1000000000000 : ℝ)*(sp_s0_20) + (495487/100000000000 : ℝ)*(sp_s0_23) + (6030163467983/1000000000000 : ℝ)*(f.failure) + (10049441399333/1000000000000 : ℝ)*(f.sum) + (12150106432463/25000000000000000000000000 : ℝ)*base62 + (207059809867/1000000000000000000000000 : ℝ)*base64 + (14916269028759/250000000000000000000000000 : ℝ)*base66 + (2597310474963/25000000000000000000000000 : ℝ)*base68 + (8180804837779/20000000000000000000000000 : ℝ)*base70 + (747702509842277/2000000000000000000000000000 : ℝ)*base72 + (607495869/10000000000000000000000 : ℝ)*base74 + (6837235481119/20000000000000000000000000 : ℝ)*base76 + (15818067285921/400000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (10303/12500000000000000 : ℝ)*base86 + (2197/12500000000000000 : ℝ)*base89 + (2197/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-9653/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9653/25000 : ℝ)*X 1 1+(-1 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5084353040878502412711/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1315735974663/200000000000 : ℝ)*(base7) + (1609059653511/1000000000000 : ℝ)*(base33) + (321793315351/200000000000 : ℝ)*(base44) + (125666193133/10000000000 : ℝ)*(base53) + (241822089323/1000000000000 : ℝ)*(base59) + (6631705187413/500000000000 : ℝ)*(major_s0_0) + (6631751725791/500000000000 : ℝ)*(major_s0_1) + (2305850715037/1000000000000 : ℝ)*(major_s0_2) + (17004463/500000000000 : ℝ)*(sp_s0_6) + (8597869/100000000000 : ℝ)*(sp_s0_13) + (3253923866107/1000000000000 : ℝ)*(sp_s0_21) + (35897635841/1000000000000 : ℝ)*(sp_s0_22) + (1776435440737/125000000000 : ℝ)*(sp_s0_23) + (461727271511/31250000000 : ℝ)*(sp_s0_27) + (9805679379409/1000000000000 : ℝ)*(f.failure) + (15820543179407/1000000000000 : ℝ)*(f.sum) + (49934798883281/100000000000000000000000000 : ℝ)*base63 + (5404826125683/50000000000000000000000000 : ℝ)*base65 + (206056618520367/2000000000000000000000000000 : ℝ)*base67 + (20086862246719/100000000000000000000000000 : ℝ)*base68 + (2750877901431/50000000000000000000000000 : ℝ)*base71 + (471146943693141/2000000000000000000000000000 : ℝ)*base72 + (402871577/1000000000000000000000 : ℝ)*base75 + (2141185008943/25000000000000000000000000 : ℝ)*base76 + (18774887021193/250000000000000000000000000 : ℝ)*base79 + (2731/12500000000000000 : ℝ)*base87 + (2731/12500000000000000 : ℝ)*base89 + (2731/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (37281/50000 : ℝ) ^ (33/8 : ℝ) ≤ (595888335402899293/2000000000000000000 : ℝ) := by
    have hpowers : (37281/50000 : ℝ)^33 ≤ (595888335402899293/2000000000000000000 : ℝ)^8 := by
      have hnat : (37281 : ℕ)^33*2000000000000000000^8 ≤ 595888335402899293^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37281 50000 595888335402899293 2000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37281/50000 : ℝ)) (X := (595888335402899293/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2595888335402899293/2000000000000000000 : ℝ) ≤ (426104375733029/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2595888335402899293/2000000000000000000 : ℝ)^8 ≤ (426104375733029/400000000000000 : ℝ)^33 := by
      have hnat : (2595888335402899293 : ℕ)^8*400000000000000^33 ≤ 426104375733029^33*2000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2595888335402899293 2000000000000000000 426104375733029 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (426104375733029/400000000000000 : ℝ)) (X := (2595888335402899293/2000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1595888335402899293/1000000000000000000 : ℝ) ≤ (11199863440663793/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1595888335402899293/1000000000000000000 : ℝ)^8 ≤ (11199863440663793/10000000000000000 : ℝ)^33 := by
      have hnat : (1595888335402899293 : ℕ)^8*10000000000000000^33 ≤ 11199863440663793^33*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1595888335402899293 1000000000000000000 11199863440663793 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11199863440663793/10000000000000000 : ℝ)) (X := (1595888335402899293/1000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(26104375733029/298248000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2))+(45604503944839/621350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (37281/50000 : ℝ)) (alpha := (26104375733029/298248000000000 : ℝ)) (beta := (45604503944839/621350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 2) ≤ (37281/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(26104375733029/298248000000000 : ℝ)*((1 : ℝ)*pair X 0 2)+(45604503944839/621350000000000 : ℝ)*((1 : ℝ)*pair X 0 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16793/20000 : ℝ) ^ (33/8 : ℝ) ≤ (48630132829514166233/100000000000000000000 : ℝ) := by
    have hpowers : (16793/20000 : ℝ)^33 ≤ (48630132829514166233/100000000000000000000 : ℝ)^8 := by
      have hnat : (16793 : ℕ)^33*100000000000000000000^8 ≤ 48630132829514166233^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16793 20000 48630132829514166233 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16793/20000 : ℝ)) (X := (48630132829514166233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (148630132829514166233/100000000000000000000 : ℝ) ≤ (11008366412521577/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (148630132829514166233/100000000000000000000 : ℝ)^8 ≤ (11008366412521577/10000000000000000 : ℝ)^33 := by
      have hnat : (148630132829514166233 : ℕ)^8*10000000000000000^33 ≤ 11008366412521577^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        148630132829514166233 100000000000000000000 11008366412521577 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11008366412521577/10000000000000000 : ℝ)) (X := (148630132829514166233/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (98630132829514166233/50000000000000000000 : ℝ) ≤ (11790297261421959/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (98630132829514166233/50000000000000000000 : ℝ)^8 ≤ (11790297261421959/10000000000000000 : ℝ)^33 := by
      have hnat : (98630132829514166233 : ℕ)^8*10000000000000000^33 ≤ 11790297261421959^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        98630132829514166233 50000000000000000000 11790297261421959 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11790297261421959/10000000000000000 : ℝ)) (X := (98630132829514166233/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0))+(1008366412521577/8396500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(390965424450191/4198250000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (16793/20000 : ℝ)) (alpha := (1008366412521577/8396500000000000 : ℝ)) (beta := (390965424450191/4198250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (16793/20000 : ℝ)*((1 : ℝ)*pair X 1 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 0)+(1008366412521577/8396500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(390965424450191/4198250000000000 : ℝ)*((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9653/25000 : ℝ) ^ (33/8 : ℝ) ≤ (1973465221780152839/100000000000000000000 : ℝ) := by
    have hpowers : (9653/25000 : ℝ)^33 ≤ (1973465221780152839/100000000000000000000 : ℝ)^8 := by
      have hnat : (9653 : ℕ)^33*100000000000000000000^8 ≤ 1973465221780152839^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9653 25000 1973465221780152839 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9653/25000 : ℝ)) (X := (1973465221780152839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101973465221780152839/100000000000000000000 : ℝ) ≤ (2511872008213139/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101973465221780152839/100000000000000000000 : ℝ)^8 ≤ (2511872008213139/2500000000000000 : ℝ)^33 := by
      have hnat : (101973465221780152839 : ℕ)^8*2500000000000000^33 ≤ 2511872008213139^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101973465221780152839 100000000000000000000 2511872008213139 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511872008213139/2500000000000000 : ℝ)) (X := (101973465221780152839/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51973465221780152839/50000000000000000000 : ℝ) ≤ (10094284855857151/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (51973465221780152839/50000000000000000000 : ℝ)^8 ≤ (10094284855857151/10000000000000000 : ℝ)^33 := by
      have hnat : (51973465221780152839 : ℕ)^8*10000000000000000^33 ≤ 10094284855857151^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51973465221780152839 50000000000000000000 10094284855857151 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10094284855857151/10000000000000000 : ℝ)) (X := (51973465221780152839/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 1+X 1 1))+(11872008213139/965300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 1 2))+(9359364600919/772240000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (9653/25000 : ℝ)) (alpha := (11872008213139/965300000000000 : ℝ)) (beta := (9359364600919/772240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 2) ≤ (9653/25000 : ℝ)*((-1 : ℝ)*pair X 2 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 1)+(11872008213139/965300000000000 : ℝ)*((1 : ℝ)*pair X 2 2)+(9359364600919/772240000000000 : ℝ)*((-1 : ℝ)*pair X 2 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-108459/10000000000 : ℝ)*X 0 0+(-31236109/31250000 : ℝ)*X 0 1+(1047979/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((30451047/2000000000 : ℝ)*X 1 0+(-4799399081/5000000000 : ℝ)*X 1 1+(-979716283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((9695160043/10000000000 : ℝ)*X 2 0+(3162641/250000000 : ℝ)*X 2 1+(793353809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((9433232591/10000000000 : ℝ)*X 0 0+(-159436603/5000000000 : ℝ)*X 0 1+(1198812087/10000000000 : ℝ)*X 0 2+(9433232591/10000000000 : ℝ)*X 1 0+(-159436603/5000000000 : ℝ)*X 1 1+(1198812087/10000000000 : ℝ)*X 1 2+(9433232591/10000000000 : ℝ)*X 2 0+(-159436603/5000000000 : ℝ)*X 2 1+(1198812087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201308_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-2182170510561557413384768895199/372654662500000000000000000000 : ℝ) := by norm_num
    linear_combination (139854981541/250000000000 : ℝ)*(base7) + (1615983/1000000000000 : ℝ)*(base10) + (26304287359/250000000000 : ℝ)*(base33) + (41/10000000000 : ℝ)*(base39) + (223803639/2000000000 : ℝ)*(base44) + (945983545499/1000000000000 : ℝ)*(base53) + (16215304533/500000000000 : ℝ)*(base59) + (2773/500000000000 : ℝ)*(ratio_s0_1) + (352875712641/250000000000 : ℝ)*(major_s1_0) + (2809636361/2000000000 : ℝ)*(major_s1_1) + (570736454501/1000000000000 : ℝ)*(major_s1_2) + (327846828383/500000000000 : ℝ)*(sp_s1_0) + (219288151907/500000000000 : ℝ)*(sp_s1_1) + (1496461668813/1000000000000 : ℝ)*(sp_s1_2) + (180939763333/125000000000 : ℝ)*(sp_s1_6) + (1601678818249/1000000000000 : ℝ)*(f.sum) + (572229813569661/772240000000000000000000000 : ℝ)*base63 + (4661757697281/5997500000000000000000000 : ℝ)*base64 + (680887401466696259/2315754700000000000000000000000 : ℝ)*base66 + (8188064214471/154448000000000000000000000 : ℝ)*base68 + (5230209901837/19417187500000000000000000 : ℝ)*base70 + (663732401413559943/11995783100000000000000000000000 : ℝ)*base73 + (4633074617/10000000000000000000000 : ℝ)*base75 + (7303544553286399/23290916406250000000000000000 : ℝ)*base76 + (1917166999673421/5962474600000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p001_b123 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 308 ≤ c.val) (hhi : c.val < 309)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by
  have hc : c=308 := by omega
  rcases hc with rfl
  · exact collision_c201308 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 308 ≤ c.val) (hhi : c.val < 309)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b123 p hpa hpb c hlo hhi X hX

#print axioms solution
