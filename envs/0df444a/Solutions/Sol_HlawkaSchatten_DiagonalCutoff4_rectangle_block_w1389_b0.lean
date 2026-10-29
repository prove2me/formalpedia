-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1389_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:04.113922+00:00
-- url     : https://prove2.me/submissions/07c237cd-7a6d-4d2a-88cd-8b7cba0c849e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1389_s0_0 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-356337047/2000000000 : ℝ)*x 0 + (5976863123/10000000000 : ℝ)*x 1 + (2410999151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356337047/2000000000 : ℝ)^4349 ≤ (5236962436793/50000000000000 : ℝ)^3325 := by
    have hnat : (356337047 : ℕ)^4349*50000000000000^3325 ≤ 5236962436793^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356337047 2000000000 5236962436793 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5976863123/10000000000 : ℝ)^4349 ≤ (510074734553/1000000000000 : ℝ)^3325 := by
    have hnat : (5976863123 : ℕ)^4349*1000000000000^3325 ≤ 510074734553^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976863123 10000000000 510074734553 1000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2410999151/5000000000 : ℝ)^4349 ≤ (3851860165287/10000000000000 : ℝ)^3325 := by
    have hnat : (2410999151 : ℕ)^4349*10000000000000^3325 ≤ 3851860165287^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410999151 5000000000 3851860165287 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356337047/2000000000 : ℝ), (5976863123/10000000000 : ℝ), (2410999151/5000000000 : ℝ)] ![(5236962436793/50000000000000 : ℝ), (510074734553/1000000000000 : ℝ), (3851860165287/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356337047/2000000000 : ℝ)|^4349 ≤ (5236962436793/50000000000000 : ℝ)^3325
        have hw : |(-356337047/2000000000 : ℝ)|=(356337047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5976863123/10000000000 : ℝ)|^4349 ≤ (510074734553/1000000000000 : ℝ)^3325
        have hw : |(5976863123/10000000000 : ℝ)|=(5976863123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2410999151/5000000000 : ℝ)|^4349 ≤ (3851860165287/10000000000000 : ℝ)^3325
        have hw : |(2410999151/5000000000 : ℝ)|=(2410999151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_1 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343534799/625000000 : ℝ)*x 0 + (-243589553/1000000000 : ℝ)*x 1 + (4821998411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343534799/625000000 : ℝ)^4349 ≤ (182854843509/400000000000 : ℝ)^3325 := by
    have hnat : (343534799 : ℕ)^4349*400000000000^3325 ≤ 182854843509^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343534799 625000000 182854843509 400000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243589553/1000000000 : ℝ)^4349 ≤ (15767686322017/100000000000000 : ℝ)^3325 := by
    have hnat : (243589553 : ℕ)^4349*100000000000000^3325 ≤ 15767686322017^3325*1000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243589553 1000000000 15767686322017 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4821998411/10000000000 : ℝ)^4349 ≤ (38518602791723/100000000000000 : ℝ)^3325 := by
    have hnat : (4821998411 : ℕ)^4349*100000000000000^3325 ≤ 38518602791723^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821998411 10000000000 38518602791723 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343534799/625000000 : ℝ), (-243589553/1000000000 : ℝ), (4821998411/10000000000 : ℝ)] ![(182854843509/400000000000 : ℝ), (15767686322017/100000000000000 : ℝ), (38518602791723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343534799/625000000 : ℝ)|^4349 ≤ (182854843509/400000000000 : ℝ)^3325
        have hw : |(343534799/625000000 : ℝ)|=(343534799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243589553/1000000000 : ℝ)|^4349 ≤ (15767686322017/100000000000000 : ℝ)^3325
        have hw : |(-243589553/1000000000 : ℝ)|=(243589553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4821998411/10000000000 : ℝ)|^4349 ≤ (38518602791723/100000000000000 : ℝ)^3325
        have hw : |(4821998411/10000000000 : ℝ)|=(4821998411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_2 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099311359/2000000000 : ℝ)*x 0 + (301374899/625000000 : ℝ)*x 1 + (-608973887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099311359/2000000000 : ℝ)^4349 ≤ (4571371099691/10000000000000 : ℝ)^3325 := by
    have hnat : (1099311359 : ℕ)^4349*10000000000000^3325 ≤ 4571371099691^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099311359 2000000000 4571371099691 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301374899/625000000 : ℝ)^4349 ≤ (19259301254811/50000000000000 : ℝ)^3325 := by
    have hnat : (301374899 : ℕ)^4349*50000000000000^3325 ≤ 19259301254811^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301374899 625000000 19259301254811 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608973887/2500000000 : ℝ)^4349 ≤ (3153537294883/20000000000000 : ℝ)^3325 := by
    have hnat : (608973887 : ℕ)^4349*20000000000000^3325 ≤ 3153537294883^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608973887 2500000000 3153537294883 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099311359/2000000000 : ℝ), (301374899/625000000 : ℝ), (-608973887/2500000000 : ℝ)] ![(4571371099691/10000000000000 : ℝ), (19259301254811/50000000000000 : ℝ), (3153537294883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099311359/2000000000 : ℝ)|^4349 ≤ (4571371099691/10000000000000 : ℝ)^3325
        have hw : |(1099311359/2000000000 : ℝ)|=(1099311359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301374899/625000000 : ℝ)|^4349 ≤ (19259301254811/50000000000000 : ℝ)^3325
        have hw : |(301374899/625000000 : ℝ)|=(301374899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-608973887/2500000000 : ℝ)|^4349 ≤ (3153537294883/20000000000000 : ℝ)^3325
        have hw : |(-608973887/2500000000 : ℝ)|=(608973887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_3 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2085896749/5000000000 : ℝ)*x 0 + (3104563331/10000000000 : ℝ)*x 1 + (1391588669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085896749/5000000000 : ℝ)^4349 ≤ (6374169981317/20000000000000 : ℝ)^3325 := by
    have hnat : (2085896749 : ℕ)^4349*20000000000000^3325 ≤ 6374169981317^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085896749 5000000000 6374169981317 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104563331/10000000000 : ℝ)^4349 ≤ (4330937921317/20000000000000 : ℝ)^3325 := by
    have hnat : (3104563331 : ℕ)^4349*20000000000000^3325 ≤ 4330937921317^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104563331 10000000000 4330937921317 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1391588669/2500000000 : ℝ)^4349 ≤ (46474460476769/100000000000000 : ℝ)^3325 := by
    have hnat : (1391588669 : ℕ)^4349*100000000000000^3325 ≤ 46474460476769^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391588669 2500000000 46474460476769 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085896749/5000000000 : ℝ), (3104563331/10000000000 : ℝ), (1391588669/2500000000 : ℝ)] ![(6374169981317/20000000000000 : ℝ), (4330937921317/20000000000000 : ℝ), (46474460476769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085896749/5000000000 : ℝ)|^4349 ≤ (6374169981317/20000000000000 : ℝ)^3325
        have hw : |(2085896749/5000000000 : ℝ)|=(2085896749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104563331/10000000000 : ℝ)|^4349 ≤ (4330937921317/20000000000000 : ℝ)^3325
        have hw : |(3104563331/10000000000 : ℝ)|=(3104563331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1391588669/2500000000 : ℝ)|^4349 ≤ (46474460476769/100000000000000 : ℝ)^3325
        have hw : |(1391588669/2500000000 : ℝ)|=(1391588669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_4 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-446475149/2500000000 : ℝ)*x 0 + (303227013/625000000 : ℝ)*x 1 + (5946170057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446475149/2500000000 : ℝ)^4349 ≤ (5253174530893/50000000000000 : ℝ)^3325 := by
    have hnat : (446475149 : ℕ)^4349*50000000000000^3325 ≤ 5253174530893^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446475149 2500000000 5253174530893 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303227013/625000000 : ℝ)^4349 ≤ (38828515031739/100000000000000 : ℝ)^3325 := by
    have hnat : (303227013 : ℕ)^4349*100000000000000^3325 ≤ 38828515031739^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303227013 625000000 38828515031739 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5946170057/10000000000 : ℝ)^4349 ≤ (50665135883131/100000000000000 : ℝ)^3325 := by
    have hnat : (5946170057 : ℕ)^4349*100000000000000^3325 ≤ 50665135883131^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946170057 10000000000 50665135883131 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446475149/2500000000 : ℝ), (303227013/625000000 : ℝ), (5946170057/10000000000 : ℝ)] ![(5253174530893/50000000000000 : ℝ), (38828515031739/100000000000000 : ℝ), (50665135883131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446475149/2500000000 : ℝ)|^4349 ≤ (5253174530893/50000000000000 : ℝ)^3325
        have hw : |(-446475149/2500000000 : ℝ)|=(446475149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303227013/625000000 : ℝ)|^4349 ≤ (38828515031739/100000000000000 : ℝ)^3325
        have hw : |(303227013/625000000 : ℝ)|=(303227013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5946170057/10000000000 : ℝ)|^4349 ≤ (50665135883131/100000000000000 : ℝ)^3325
        have hw : |(5946170057/10000000000 : ℝ)|=(5946170057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_5 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036309847/2000000000 : ℝ)*x 0 + (-81982777/625000000 : ℝ)*x 1 + (118923361/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036309847/2000000000 : ℝ)^4349 ≤ (42317673419249/100000000000000 : ℝ)^3325 := by
    have hnat : (1036309847 : ℕ)^4349*100000000000000^3325 ≤ 42317673419249^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036309847 2000000000 42317673419249 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81982777/625000000 : ℝ)^4349 ≤ (7017213043383/100000000000000 : ℝ)^3325 := by
    have hnat : (81982777 : ℕ)^4349*100000000000000^3325 ≤ 7017213043383^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81982777 625000000 7017213043383 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118923361/200000000 : ℝ)^4349 ≤ (25332556757827/50000000000000 : ℝ)^3325 := by
    have hnat : (118923361 : ℕ)^4349*50000000000000^3325 ≤ 25332556757827^3325*200000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118923361 200000000 25332556757827 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036309847/2000000000 : ℝ), (-81982777/625000000 : ℝ), (118923361/200000000 : ℝ)] ![(42317673419249/100000000000000 : ℝ), (7017213043383/100000000000000 : ℝ), (25332556757827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036309847/2000000000 : ℝ)|^4349 ≤ (42317673419249/100000000000000 : ℝ)^3325
        have hw : |(1036309847/2000000000 : ℝ)|=(1036309847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81982777/625000000 : ℝ)|^4349 ≤ (7017213043383/100000000000000 : ℝ)^3325
        have hw : |(-81982777/625000000 : ℝ)|=(81982777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118923361/200000000 : ℝ)|^4349 ≤ (25332556757827/50000000000000 : ℝ)^3325
        have hw : |(118923361/200000000 : ℝ)|=(118923361/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_6 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40480823/78125000 : ℝ)*x 0 + (297308651/500000000 : ℝ)*x 1 + (-655861229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40480823/78125000 : ℝ)^4349 ≤ (4231763185489/10000000000000 : ℝ)^3325 := by
    have hnat : (40480823 : ℕ)^4349*10000000000000^3325 ≤ 4231763185489^3325*78125000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40480823 78125000 4231763185489 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297308651/500000000 : ℝ)^4349 ≤ (2026606756199/4000000000000 : ℝ)^3325 := by
    have hnat : (297308651 : ℕ)^4349*4000000000000^3325 ≤ 2026606756199^3325*500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297308651 500000000 2026606756199 4000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655861229/5000000000 : ℝ)^4349 ≤ (1403439846211/20000000000000 : ℝ)^3325 := by
    have hnat : (655861229 : ℕ)^4349*20000000000000^3325 ≤ 1403439846211^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655861229 5000000000 1403439846211 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40480823/78125000 : ℝ), (297308651/500000000 : ℝ), (-655861229/5000000000 : ℝ)] ![(4231763185489/10000000000000 : ℝ), (2026606756199/4000000000000 : ℝ), (1403439846211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40480823/78125000 : ℝ)|^4349 ≤ (4231763185489/10000000000000 : ℝ)^3325
        have hw : |(40480823/78125000 : ℝ)|=(40480823/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297308651/500000000 : ℝ)|^4349 ≤ (2026606756199/4000000000000 : ℝ)^3325
        have hw : |(297308651/500000000 : ℝ)|=(297308651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-655861229/5000000000 : ℝ)|^4349 ≤ (1403439846211/20000000000000 : ℝ)^3325
        have hw : |(-655861229/5000000000 : ℝ)|=(655861229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s0_7 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180771269/10000000000 : ℝ)*x 0 + (5503187281/10000000000 : ℝ)*x 1 + (3169994241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180771269/10000000000 : ℝ)^4349 ≤ (31960588848421/100000000000000 : ℝ)^3325 := by
    have hnat : (4180771269 : ℕ)^4349*100000000000000^3325 ≤ 31960588848421^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180771269 10000000000 31960588848421 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503187281/10000000000 : ℝ)^4349 ≤ (45785851558693/100000000000000 : ℝ)^3325 := by
    have hnat : (5503187281 : ℕ)^4349*100000000000000^3325 ≤ 45785851558693^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503187281 10000000000 45785851558693 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169994241/10000000000 : ℝ)^4349 ≤ (11126779791553/50000000000000 : ℝ)^3325 := by
    have hnat : (3169994241 : ℕ)^4349*50000000000000^3325 ≤ 11126779791553^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169994241 10000000000 11126779791553 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180771269/10000000000 : ℝ), (5503187281/10000000000 : ℝ), (3169994241/10000000000 : ℝ)] ![(31960588848421/100000000000000 : ℝ), (45785851558693/100000000000000 : ℝ), (11126779791553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180771269/10000000000 : ℝ)|^4349 ≤ (31960588848421/100000000000000 : ℝ)^3325
        have hw : |(4180771269/10000000000 : ℝ)|=(4180771269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503187281/10000000000 : ℝ)|^4349 ≤ (45785851558693/100000000000000 : ℝ)^3325
        have hw : |(5503187281/10000000000 : ℝ)|=(5503187281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169994241/10000000000 : ℝ)|^4349 ≤ (11126779791553/50000000000000 : ℝ)^3325
        have hw : |(3169994241/10000000000 : ℝ)|=(3169994241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1389_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1761/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26537/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (1087/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1087 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1087*1^256 ≤ 0^256*1^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1087/256 : ℝ) ≤ (2043193114219560119/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1087 ≤ (2043193114219560119/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1087*100000000000000000000^256 ≤ 2043193114219560119^256*5^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2043193114219560119 100000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2043193114219560119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1087 := by
      have hnat : (1 : ℕ)^256*1^1087 ≤ 1^1087*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102043193114219560119/100000000000000000000 : ℝ) ≤ (10047748000811377/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (102043193114219560119/100000000000000000000 : ℝ)^256 ≤ (10047748000811377/10000000000000000 : ℝ)^1087 := by
      have hnat : (102043193114219560119 : ℕ)^256*10000000000000000^1087 ≤ 10047748000811377^1087*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102043193114219560119 100000000000000000000 10047748000811377 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047748000811377/10000000000000000 : ℝ)) (X := (102043193114219560119/100000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52043193114219560119/50000000000000000000 : ℝ) ≤ (5047748000811377/5000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (52043193114219560119/50000000000000000000 : ℝ)^256 ≤ (5047748000811377/5000000000000000 : ℝ)^1087 := by
      have hnat : (52043193114219560119 : ℕ)^256*5000000000000000^1087 ≤ 5047748000811377^1087*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52043193114219560119 50000000000000000000 5047748000811377 5000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047748000811377/5000000000000000 : ℝ)) (X := (52043193114219560119/50000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47748000811377/4000000000000000 : ℝ)*(0 : ℝ))^(1087/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(47748000811377/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2043193114219560119/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47748000811377/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1087/256 : ℝ) := by
    rw [show (1 : ℝ)+(47748000811377/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047748000811377/10000000000000000 : ℝ) by norm_num, show 1+(2043193114219560119/100000000000000000000 : ℝ)+(0 : ℝ)=(102043193114219560119/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2043193114219560119/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47748000811377/4000000000000000 : ℝ)*(2/5 : ℝ))^(1087/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(47748000811377/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047748000811377/5000000000000000 : ℝ) by norm_num, show 1+2*(2043193114219560119/100000000000000000000 : ℝ)=(52043193114219560119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47748000811377/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47748000811377/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47748000811377/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47748000811377/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47748000811377/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47748000811377/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-356337047/2000000000 : ℝ)*X 0 0+(5976863123/10000000000 : ℝ)*X 0 1+(2410999151/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343534799/625000000 : ℝ)*X 1 0+(-243589553/1000000000 : ℝ)*X 1 1+(4821998411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1099311359/2000000000 : ℝ)*X 2 0+(301374899/625000000 : ℝ)*X 2 1+(-608973887/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2085896749/5000000000 : ℝ)*X 0 0+(3104563331/10000000000 : ℝ)*X 0 1+(1391588669/2500000000 : ℝ)*X 0 2+(2085896749/5000000000 : ℝ)*X 1 0+(3104563331/10000000000 : ℝ)*X 1 1+(1391588669/2500000000 : ℝ)*X 1 2+(2085896749/5000000000 : ℝ)*X 2 0+(3104563331/10000000000 : ℝ)*X 2 1+(1391588669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-446475149/2500000000 : ℝ)*X 0 0+(303227013/625000000 : ℝ)*X 0 1+(5946170057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036309847/2000000000 : ℝ)*X 1 0+(-81982777/625000000 : ℝ)*X 1 1+(118923361/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((40480823/78125000 : ℝ)*X 2 0+(297308651/500000000 : ℝ)*X 2 1+(-655861229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180771269/10000000000 : ℝ)*X 0 0+(5503187281/10000000000 : ℝ)*X 0 1+(3169994241/10000000000 : ℝ)*X 0 2+(4180771269/10000000000 : ℝ)*X 1 0+(5503187281/10000000000 : ℝ)*X 1 1+(3169994241/10000000000 : ℝ)*X 1 2+(4180771269/10000000000 : ℝ)*X 2 0+(5503187281/10000000000 : ℝ)*X 2 1+(3169994241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (320300007802097209272771/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24665851/50000000000000 : ℝ)*(base1) + (749562663/50000000000000 : ℝ)*(base19) + (1500858233/100000000000000 : ℝ)*(base23) + (46823573/25000000000000 : ℝ)*(upper3) + (182998991/100000000000000 : ℝ)*(upper5) + (318031339902853/50000000000000 : ℝ)*(major0) + (318031339902853/50000000000000 : ℝ)*(major1) + (318031339902853/50000000000000 : ℝ)*(major2) + (865907078413411/100000000000000 : ℝ)*(sp0) + (6764926885221/781250000000 : ℝ)*(sp1) + (865910639575381/100000000000000 : ℝ)*(sp2) + (203105271513719/50000000000000 : ℝ)*(sp3) + (1022270381/20000000000000 : ℝ)*(sp4) + (1206642657/50000000000000 : ℝ)*(sp7) + (203106502822227/50000000000000 : ℝ)*(f.failure) + (432956070216807/50000000000000 : ℝ)*(f.sum) + (275028394658581/100000000000000000000000000000 : ℝ)*base65 + (50467156158581/200000000000000000000000000000 : ℝ)*base67 + (944637663358581/200000000000000000000000000000 : ℝ)*base69 + (580186880758581/200000000000000000000000000000 : ℝ)*base71 + (231578899958581/100000000000000000000000000000 : ℝ)*base73 + (1204598931158581/200000000000000000000000000000 : ℝ)*base75 + (1518499260158581/200000000000000000000000000000 : ℝ)*base77 + (179770053958581/200000000000000000000000000000 : ℝ)*base79 + (460603059758581/100000000000000000000000000000 : ℝ)*base81 + (11294891/2500000000000000000000 : ℝ)*base90 + (11294891/2500000000000000000000 : ℝ)*base92 + (11294891/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21113263562910614558823/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (698858041/50000000000000 : ℝ)*(base19) + (98392497/6250000000000 : ℝ)*(base23) + (85459887/25000000000000 : ℝ)*(base39) + (9449157/4000000000000 : ℝ)*(upper2) + (474847/160000000000 : ℝ)*(upper5) + (671110782460547/100000000000000 : ℝ)*(major0) + (671110782460547/100000000000000 : ℝ)*(major1) + (671110440620999/100000000000000 : ℝ)*(major2) + (3409148181/100000000000000 : ℝ)*(sp1) + (575752599/12500000000000 : ℝ)*(sp2) + (228406232346877/25000000000000 : ℝ)*(sp4) + (182724024504649/20000000000000 : ℝ)*(sp5) + (114202386365789/12500000000000 : ℝ)*(sp6) + (428596012183853/100000000000000 : ℝ)*(sp7) + (428596012183853/100000000000000 : ℝ)*(f.failure) + (57101579451691/6250000000000 : ℝ)*(f.sum) + (1079328820025579/200000000000000000000000000000 : ℝ)*base66 + (1119300798494377/400000000000000000000000000000 : ℝ)*base68 + (1653558920356781/400000000000000000000000000000 : ℝ)*base70 + (2925527030094377/400000000000000000000000000000 : ℝ)*base72 + (203219933174421/200000000000000000000000000000 : ℝ)*base73 + (464524794356781/400000000000000000000000000000 : ℝ)*base76 + (3283580478756781/400000000000000000000000000000 : ℝ)*base78 + (1860533933156781/400000000000000000000000000000 : ℝ)*base80 + (176791840956781/200000000000000000000000000000 : ℝ)*base82 + (30238251/5000000000000000000000 : ℝ)*base89 + (30238251/5000000000000000000000 : ℝ)*base91 + (30238251/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1389_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1761/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26537/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1389_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1389_s1_0 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959740099/10000000000 : ℝ)*x 0 + (702710481/1250000000 : ℝ)*x 1 + (15822167/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959740099/10000000000 : ℝ)^4349 ≤ (1186361099313/10000000000000 : ℝ)^3325 := by
    have hnat : (1959740099 : ℕ)^4349*10000000000000^3325 ≤ 1186361099313^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959740099 10000000000 1186361099313 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702710481/1250000000 : ℝ)^4349 ≤ (23539801810837/50000000000000 : ℝ)^3325 := by
    have hnat : (702710481 : ℕ)^4349*50000000000000^3325 ≤ 23539801810837^3325*1250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702710481 1250000000 23539801810837 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15822167/31250000 : ℝ)^4349 ≤ (20528392689287/50000000000000 : ℝ)^3325 := by
    have hnat : (15822167 : ℕ)^4349*50000000000000^3325 ≤ 20528392689287^3325*31250000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15822167 31250000 20528392689287 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959740099/10000000000 : ℝ), (702710481/1250000000 : ℝ), (15822167/31250000 : ℝ)] ![(1186361099313/10000000000000 : ℝ), (23539801810837/50000000000000 : ℝ), (20528392689287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959740099/10000000000 : ℝ)|^4349 ≤ (1186361099313/10000000000000 : ℝ)^3325
        have hw : |(-1959740099/10000000000 : ℝ)|=(1959740099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702710481/1250000000 : ℝ)|^4349 ≤ (23539801810837/50000000000000 : ℝ)^3325
        have hw : |(702710481/1250000000 : ℝ)|=(702710481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15822167/31250000 : ℝ)|^4349 ≤ (20528392689287/50000000000000 : ℝ)^3325
        have hw : |(15822167/31250000 : ℝ)|=(15822167/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_1 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700431693/5000000000 : ℝ)*x 0 + (-1128328623/5000000000 : ℝ)*x 1 + (1265773717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700431693/5000000000 : ℝ)^4349 ≤ (11168887334483/25000000000000 : ℝ)^3325 := by
    have hnat : (2700431693 : ℕ)^4349*25000000000000^3325 ≤ 11168887334483^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700431693 5000000000 11168887334483 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128328623/5000000000 : ℝ)^4349 ≤ (14267650117839/100000000000000 : ℝ)^3325 := by
    have hnat : (1128328623 : ℕ)^4349*100000000000000^3325 ≤ 14267650117839^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128328623 5000000000 14267650117839 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265773717/2500000000 : ℝ)^4349 ≤ (41056800524471/100000000000000 : ℝ)^3325 := by
    have hnat : (1265773717 : ℕ)^4349*100000000000000^3325 ≤ 41056800524471^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265773717 2500000000 41056800524471 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700431693/5000000000 : ℝ), (-1128328623/5000000000 : ℝ), (1265773717/2500000000 : ℝ)] ![(11168887334483/25000000000000 : ℝ), (14267650117839/100000000000000 : ℝ), (41056800524471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700431693/5000000000 : ℝ)|^4349 ≤ (11168887334483/25000000000000 : ℝ)^3325
        have hw : |(2700431693/5000000000 : ℝ)|=(2700431693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128328623/5000000000 : ℝ)|^4349 ≤ (14267650117839/100000000000000 : ℝ)^3325
        have hw : |(-1128328623/5000000000 : ℝ)|=(1128328623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1265773717/2500000000 : ℝ)|^4349 ≤ (41056800524471/100000000000000 : ℝ)^3325
        have hw : |(1265773717/2500000000 : ℝ)|=(1265773717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_2 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350216057/2500000000 : ℝ)*x 0 + (5063093621/10000000000 : ℝ)*x 1 + (-141041109/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350216057/2500000000 : ℝ)^4349 ≤ (22337779223947/50000000000000 : ℝ)^3325 := by
    have hnat : (1350216057 : ℕ)^4349*50000000000000^3325 ≤ 22337779223947^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350216057 2500000000 22337779223947 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5063093621/10000000000 : ℝ)^4349 ≤ (41056787298327/100000000000000 : ℝ)^3325 := by
    have hnat : (5063093621 : ℕ)^4349*100000000000000^3325 ≤ 41056787298327^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063093621 10000000000 41056787298327 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141041109/625000000 : ℝ)^4349 ≤ (14267654236101/100000000000000 : ℝ)^3325 := by
    have hnat : (141041109 : ℕ)^4349*100000000000000^3325 ≤ 14267654236101^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141041109 625000000 14267654236101 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350216057/2500000000 : ℝ), (5063093621/10000000000 : ℝ), (-141041109/625000000 : ℝ)] ![(22337779223947/50000000000000 : ℝ), (41056787298327/100000000000000 : ℝ), (14267654236101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350216057/2500000000 : ℝ)|^4349 ≤ (22337779223947/50000000000000 : ℝ)^3325
        have hw : |(1350216057/2500000000 : ℝ)|=(1350216057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5063093621/10000000000 : ℝ)|^4349 ≤ (41056787298327/100000000000000 : ℝ)^3325
        have hw : |(5063093621/10000000000 : ℝ)|=(5063093621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141041109/625000000 : ℝ)|^4349 ≤ (14267654236101/100000000000000 : ℝ)^3325
        have hw : |(-141041109/625000000 : ℝ)|=(141041109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_3 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283879957/10000000000 : ℝ)*x 0 + (3726084637/10000000000 : ℝ)*x 1 + (4916811251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283879957/10000000000 : ℝ)^4349 ≤ (8248866211833/25000000000000 : ℝ)^3325 := by
    have hnat : (4283879957 : ℕ)^4349*25000000000000^3325 ≤ 8248866211833^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283879957 10000000000 8248866211833 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726084637/10000000000 : ℝ)^4349 ≤ (6873080891191/25000000000000 : ℝ)^3325 := by
    have hnat : (3726084637 : ℕ)^4349*25000000000000^3325 ≤ 6873080891191^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726084637 10000000000 6873080891191 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4916811251/10000000000 : ℝ)^4349 ≤ (39512211575963/100000000000000 : ℝ)^3325 := by
    have hnat : (4916811251 : ℕ)^4349*100000000000000^3325 ≤ 39512211575963^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4916811251 10000000000 39512211575963 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283879957/10000000000 : ℝ), (3726084637/10000000000 : ℝ), (4916811251/10000000000 : ℝ)] ![(8248866211833/25000000000000 : ℝ), (6873080891191/25000000000000 : ℝ), (39512211575963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283879957/10000000000 : ℝ)|^4349 ≤ (8248866211833/25000000000000 : ℝ)^3325
        have hw : |(4283879957/10000000000 : ℝ)|=(4283879957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3726084637/10000000000 : ℝ)|^4349 ≤ (6873080891191/25000000000000 : ℝ)^3325
        have hw : |(3726084637/10000000000 : ℝ)|=(3726084637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4916811251/10000000000 : ℝ)|^4349 ≤ (39512211575963/100000000000000 : ℝ)^3325
        have hw : |(4916811251/10000000000 : ℝ)|=(4916811251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_4 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-490049219/2500000000 : ℝ)*x 0 + (1013970493/2000000000 : ℝ)*x 1 + (1403701589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490049219/2500000000 : ℝ)^4349 ≤ (2966806972219/25000000000000 : ℝ)^3325 := by
    have hnat : (490049219 : ℕ)^4349*25000000000000^3325 ≤ 2966806972219^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490049219 2500000000 2966806972219 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013970493/2000000000 : ℝ)^4349 ≤ (4112848882811/10000000000000 : ℝ)^3325 := by
    have hnat : (1013970493 : ℕ)^4349*10000000000000^3325 ≤ 4112848882811^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013970493 2000000000 4112848882811 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403701589/2500000000 : ℝ)^4349 ≤ (470042832617/1000000000000 : ℝ)^3325 := by
    have hnat : (1403701589 : ℕ)^4349*1000000000000^3325 ≤ 470042832617^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403701589 2500000000 470042832617 1000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490049219/2500000000 : ℝ), (1013970493/2000000000 : ℝ), (1403701589/2500000000 : ℝ)] ![(2966806972219/25000000000000 : ℝ), (4112848882811/10000000000000 : ℝ), (470042832617/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490049219/2500000000 : ℝ)|^4349 ≤ (2966806972219/25000000000000 : ℝ)^3325
        have hw : |(-490049219/2500000000 : ℝ)|=(490049219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013970493/2000000000 : ℝ)|^4349 ≤ (4112848882811/10000000000000 : ℝ)^3325
        have hw : |(1013970493/2000000000 : ℝ)|=(1013970493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1403701589/2500000000 : ℝ)|^4349 ≤ (470042832617/1000000000000 : ℝ)^3325
        have hw : |(1403701589/2500000000 : ℝ)|=(1403701589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_5 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262768191/500000000 : ℝ)*x 0 + (-1704945589/10000000000 : ℝ)*x 1 + (5614806393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262768191/500000000 : ℝ)^4349 ≤ (43107898157529/100000000000000 : ℝ)^3325 := by
    have hnat : (262768191 : ℕ)^4349*100000000000000^3325 ≤ 43107898157529^3325*500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262768191 500000000 43107898157529 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1704945589/10000000000 : ℝ)^4349 ≤ (1977563633629/20000000000000 : ℝ)^3325 := by
    have hnat : (1704945589 : ℕ)^4349*20000000000000^3325 ≤ 1977563633629^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704945589 10000000000 1977563633629 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5614806393/10000000000 : ℝ)^4349 ≤ (47004283666837/100000000000000 : ℝ)^3325 := by
    have hnat : (5614806393 : ℕ)^4349*100000000000000^3325 ≤ 47004283666837^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614806393 10000000000 47004283666837 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262768191/500000000 : ℝ), (-1704945589/10000000000 : ℝ), (5614806393/10000000000 : ℝ)] ![(43107898157529/100000000000000 : ℝ), (1977563633629/20000000000000 : ℝ), (47004283666837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262768191/500000000 : ℝ)|^4349 ≤ (43107898157529/100000000000000 : ℝ)^3325
        have hw : |(262768191/500000000 : ℝ)|=(262768191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1704945589/10000000000 : ℝ)|^4349 ≤ (1977563633629/20000000000000 : ℝ)^3325
        have hw : |(-1704945589/10000000000 : ℝ)|=(1704945589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5614806393/10000000000 : ℝ)|^4349 ≤ (47004283666837/100000000000000 : ℝ)^3325
        have hw : |(5614806393/10000000000 : ℝ)|=(5614806393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_6 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210214569/400000000 : ℝ)*x 0 + (22459227/40000000 : ℝ)*x 1 + (-3409889/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210214569/400000000 : ℝ)^4349 ≤ (431079025027/1000000000000 : ℝ)^3325 := by
    have hnat : (210214569 : ℕ)^4349*1000000000000^3325 ≤ 431079025027^3325*400000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210214569 400000000 431079025027 1000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22459227/40000000 : ℝ)^4349 ≤ (5875535946983/12500000000000 : ℝ)^3325 := by
    have hnat : (22459227 : ℕ)^4349*12500000000000^3325 ≤ 5875535946983^3325*40000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22459227 40000000 5875535946983 12500000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3409889/20000000 : ℝ)^4349 ≤ (988780990747/10000000000000 : ℝ)^3325 := by
    have hnat : (3409889 : ℕ)^4349*10000000000000^3325 ≤ 988780990747^3325*20000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3409889 20000000 988780990747 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210214569/400000000 : ℝ), (22459227/40000000 : ℝ), (-3409889/20000000 : ℝ)] ![(431079025027/1000000000000 : ℝ), (5875535946983/12500000000000 : ℝ), (988780990747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210214569/400000000 : ℝ)|^4349 ≤ (431079025027/1000000000000 : ℝ)^3325
        have hw : |(210214569/400000000 : ℝ)|=(210214569/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22459227/40000000 : ℝ)|^4349 ≤ (5875535946983/12500000000000 : ℝ)^3325
        have hw : |(22459227/40000000 : ℝ)|=(22459227/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3409889/20000000 : ℝ)|^4349 ≤ (988780990747/10000000000000 : ℝ)^3325
        have hw : |(-3409889/20000000 : ℝ)|=(3409889/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s1_7 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284855187/10000000000 : ℝ)*x 0 + (4902403859/10000000000 : ℝ)*x 1 + (748148493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284855187/10000000000 : ℝ)^4349 ≤ (16502644973813/50000000000000 : ℝ)^3325 := by
    have hnat : (4284855187 : ℕ)^4349*50000000000000^3325 ≤ 16502644973813^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284855187 10000000000 16502644973813 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4902403859/10000000000 : ℝ)^4349 ≤ (39360843323459/100000000000000 : ℝ)^3325 := by
    have hnat : (4902403859 : ℕ)^4349*100000000000000^3325 ≤ 39360843323459^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902403859 10000000000 39360843323459 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748148493/2000000000 : ℝ)^4349 ≤ (27633866718337/100000000000000 : ℝ)^3325 := by
    have hnat : (748148493 : ℕ)^4349*100000000000000^3325 ≤ 27633866718337^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748148493 2000000000 27633866718337 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284855187/10000000000 : ℝ), (4902403859/10000000000 : ℝ), (748148493/2000000000 : ℝ)] ![(16502644973813/50000000000000 : ℝ), (39360843323459/100000000000000 : ℝ), (27633866718337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284855187/10000000000 : ℝ)|^4349 ≤ (16502644973813/50000000000000 : ℝ)^3325
        have hw : |(4284855187/10000000000 : ℝ)|=(4284855187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4902403859/10000000000 : ℝ)|^4349 ≤ (39360843323459/100000000000000 : ℝ)^3325
        have hw : |(4902403859/10000000000 : ℝ)|=(4902403859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748148493/2000000000 : ℝ)|^4349 ≤ (27633866718337/100000000000000 : ℝ)^3325
        have hw : |(748148493/2000000000 : ℝ)|=(748148493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1389_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1761/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (239/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1761/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1761/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1761/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1761/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1761/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1761/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1761/100000 : ℝ) ^ (1087/256 : ℝ) ≤ (222438410339/6250000000000000000 : ℝ) := by
    have hpowers : (1761/100000 : ℝ)^1087 ≤ (222438410339/6250000000000000000 : ℝ)^256 := by
      have hnat : (1761 : ℕ)^1087*6250000000000000000^256 ≤ 222438410339^256*100000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 100000 222438410339 6250000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/100000 : ℝ)) (X := (222438410339/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26537/100000 : ℝ) ^ (1087/256 : ℝ) ≤ (357783932071570469/100000000000000000000 : ℝ) := by
    have hpowers : (26537/100000 : ℝ)^1087 ≤ (357783932071570469/100000000000000000000 : ℝ)^256 := by
      have hnat : (26537 : ℕ)^1087*100000000000000000000^256 ≤ 357783932071570469^256*100000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26537 100000 357783932071570469 100000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26537/100000 : ℝ)) (X := (357783932071570469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000222438410339/3125000000000000000 : ℝ) ≤ (10000000167637113/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (3125000222438410339/3125000000000000000 : ℝ)^256 ≤ (10000000167637113/10000000000000000 : ℝ)^1087 := by
      have hnat : (3125000222438410339 : ℕ)^256*10000000000000000^1087 ≤ 10000000167637113^1087*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000222438410339 3125000000000000000 10000000167637113 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000167637113/10000000000000000 : ℝ)) (X := (3125000222438410339/3125000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100357787491086135893/100000000000000000000 : ℝ) ≤ (5004207387078807/5000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (100357787491086135893/100000000000000000000 : ℝ)^256 ≤ (5004207387078807/5000000000000000 : ℝ)^1087 := by
      have hnat : (100357787491086135893 : ℕ)^256*5000000000000000^1087 ≤ 5004207387078807^1087*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100357787491086135893 100000000000000000000 5004207387078807 5000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004207387078807/5000000000000000 : ℝ)) (X := (100357787491086135893/100000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50357783932071570469/50000000000000000000 : ℝ) ≤ (2003365876135623/2000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (50357783932071570469/50000000000000000000 : ℝ)^256 ≤ (2003365876135623/2000000000000000 : ℝ)^1087 := by
      have hnat : (50357783932071570469 : ℕ)^256*2000000000000000^1087 ≤ 2003365876135623^1087*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50357783932071570469 50000000000000000000 2003365876135623 2000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003365876135623/2000000000000000 : ℝ)) (X := (50357783932071570469/50000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(222438410339/6250000000000000000 : ℝ) ≤ ((123865183954605953583/123880000000000000000 : ℝ)+2*(8414606520501/2477600000000000 : ℝ)*(1761/100000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (123865183954605953583/123880000000000000000 : ℝ)+2*(8414606520501/2477600000000000 : ℝ)*(1761/100000 : ℝ)=(10000000167637113/10000000000000000 : ℝ) by norm_num, show 1+2*(222438410339/6250000000000000000 : ℝ)=(3125000222438410339/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(357783932071570469/100000000000000000000 : ℝ)+(222438410339/6250000000000000000 : ℝ) ≤ ((123865183954605953583/123880000000000000000 : ℝ)+(8414606520501/2477600000000000 : ℝ)*((26537/100000 : ℝ)+(1761/100000 : ℝ)))^(1087/256 : ℝ) := by
    rw [show (123865183954605953583/123880000000000000000 : ℝ)+(8414606520501/2477600000000000 : ℝ)*((26537/100000 : ℝ)+(1761/100000 : ℝ))=(5004207387078807/5000000000000000 : ℝ) by norm_num, show 1+(357783932071570469/100000000000000000000 : ℝ)+(222438410339/6250000000000000000 : ℝ)=(100357787491086135893/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(357783932071570469/100000000000000000000 : ℝ) ≤ ((123865183954605953583/123880000000000000000 : ℝ)+2*(8414606520501/2477600000000000 : ℝ)*(26537/100000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (123865183954605953583/123880000000000000000 : ℝ)+2*(8414606520501/2477600000000000 : ℝ)*(26537/100000 : ℝ)=(2003365876135623/2000000000000000 : ℝ) by norm_num, show 1+2*(357783932071570469/100000000000000000000 : ℝ)=(50357783932071570469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (123865183954605953583/123880000000000000000 : ℝ)*(X 1 0+X 2 0)+(8414606520501/2477600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (1761/100000 : ℝ)) (hi := (26537/100000 : ℝ)) (c := (123865183954605953583/123880000000000000000 : ℝ)) (alpha := (8414606520501/2477600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (123865183954605953583/123880000000000000000 : ℝ)*(X 0 1+X 2 1)+(8414606520501/2477600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (1761/100000 : ℝ)) (hi := (26537/100000 : ℝ)) (c := (123865183954605953583/123880000000000000000 : ℝ)) (alpha := (8414606520501/2477600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (123865183954605953583/123880000000000000000 : ℝ)*(X 0 2+X 1 2)+(8414606520501/2477600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (1761/100000 : ℝ)) (hi := (26537/100000 : ℝ)) (c := (123865183954605953583/123880000000000000000 : ℝ)) (alpha := (8414606520501/2477600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1959740099/10000000000 : ℝ)*X 0 0+(702710481/1250000000 : ℝ)*X 0 1+(15822167/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2700431693/5000000000 : ℝ)*X 1 0+(-1128328623/5000000000 : ℝ)*X 1 1+(1265773717/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1350216057/2500000000 : ℝ)*X 2 0+(5063093621/10000000000 : ℝ)*X 2 1+(-141041109/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283879957/10000000000 : ℝ)*X 0 0+(3726084637/10000000000 : ℝ)*X 0 1+(4916811251/10000000000 : ℝ)*X 0 2+(4283879957/10000000000 : ℝ)*X 1 0+(3726084637/10000000000 : ℝ)*X 1 1+(4916811251/10000000000 : ℝ)*X 1 2+(4283879957/10000000000 : ℝ)*X 2 0+(3726084637/10000000000 : ℝ)*X 2 1+(4916811251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-490049219/2500000000 : ℝ)*X 0 0+(1013970493/2000000000 : ℝ)*X 0 1+(1403701589/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262768191/500000000 : ℝ)*X 1 0+(-1704945589/10000000000 : ℝ)*X 1 1+(5614806393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210214569/400000000 : ℝ)*X 2 0+(22459227/40000000 : ℝ)*X 2 1+(-3409889/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284855187/10000000000 : ℝ)*X 0 0+(4902403859/10000000000 : ℝ)*X 0 1+(748148493/2000000000 : ℝ)*X 0 2+(4284855187/10000000000 : ℝ)*X 1 0+(4902403859/10000000000 : ℝ)*X 1 1+(748148493/2000000000 : ℝ)*X 1 2+(4284855187/10000000000 : ℝ)*X 2 0+(4902403859/10000000000 : ℝ)*X 2 1+(748148493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11160671034994226876425088247/3097000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (503500689/100000000000000 : ℝ)*(base19) + (833185467/100000000000000 : ℝ)*(base23) + (30724173/100000000000000 : ℝ)*(upper2) + (78373533/100000000000000 : ℝ)*(upper3) + (657516069801999/50000000000000 : ℝ)*(major0) + (657516069801999/50000000000000 : ℝ)*(major1) + (657516069801999/50000000000000 : ℝ)*(major2) + (447557145613477/25000000000000 : ℝ)*(sp0) + (1790235797563979/100000000000000 : ℝ)*(sp1) + (44755880848603/2500000000000 : ℝ)*(sp2) + (419912622471313/50000000000000 : ℝ)*(sp3) + (192965269/2500000000000 : ℝ)*(sp4) + (233935081/100000000000000 : ℝ)*(sp6) + (2613077233/100000000000000 : ℝ)*(sp7) + (839827858019859/100000000000000 : ℝ)*(f.failure) + (447559075266167/25000000000000 : ℝ)*(f.sum) + (229608309939559/61940000000000000000000000000 : ℝ)*base65 + (15896953124627562417/6194000000000000000000000000000000 : ℝ)*base67 + (5722947274575562417/6194000000000000000000000000000000 : ℝ)*base69 + (8495759533351562417/6194000000000000000000000000000000 : ℝ)*base71 + (80879525855999/61940000000000000000000000000 : ℝ)*base73 + (45727480418327562417/6194000000000000000000000000000000 : ℝ)*base75 + (54670520111297562417/6194000000000000000000000000000000 : ℝ)*base77 + (17547939754743562417/6194000000000000000000000000000000 : ℝ)*base79 + (238388817679041/61940000000000000000000000000 : ℝ)*base82 + (17799147/5000000000000000000000 : ℝ)*base90 + (17799147/5000000000000000000000 : ℝ)*base92 + (17799147/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15761456953616010822397018281/3097000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175497167/100000000000000 : ℝ)*(base1) + (340961861/25000000000000 : ℝ)*(base19) + (49793713/3125000000000 : ℝ)*(base23) + (16259431/12500000000000 : ℝ)*(upper3) + (203407377/100000000000000 : ℝ)*(upper5) + (1347927641198469/100000000000000 : ℝ)*(major0) + (1347927641198469/100000000000000 : ℝ)*(major1) + (1347927641198469/100000000000000 : ℝ)*(major2) + (3409837863/50000000000000 : ℝ)*(sp1) + (5001559307/50000000000000 : ℝ)*(sp2) + (458754788462023/25000000000000 : ℝ)*(sp4) + (367002158965551/20000000000000 : ℝ)*(sp5) + (917503690916747/50000000000000 : ℝ)*(sp6) + (860835958906639/100000000000000 : ℝ)*(sp7) + (430418067201903/50000000000000 : ℝ)*(f.failure) + (458754744587731/25000000000000 : ℝ)*(f.sum) + (14587042302911/123880000000000000000000000000 : ℝ)*base66 + (32077826951874885573/12388000000000000000000000000000000 : ℝ)*base68 + (61740040731802885573/12388000000000000000000000000000000 : ℝ)*base70 + (45885642241298885573/12388000000000000000000000000000000 : ℝ)*base72 + (300915409066169/123880000000000000000000000000 : ℝ)*base73 + (198287255486630885573/12388000000000000000000000000000000 : ℝ)*base76 + (73501232561973114427/12388000000000000000000000000000000 : ℝ)*base77 + (40443431137306885573/12388000000000000000000000000000000 : ℝ)*base80 + (247737801804751/123880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6632601/2500000000000000000000 : ℝ)*base89 + (6632601/2500000000000000000000 : ℝ)*base91 + (6632601/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1389_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1761/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (239/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1389_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1389_s2_0 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249495771/1250000000 : ℝ)*x 0 + (1366889561/2500000000 : ℝ)*x 1 + (2596976403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249495771/1250000000 : ℝ)^4349 ≤ (12151262468273/100000000000000 : ℝ)^3325 := by
    have hnat : (249495771 : ℕ)^4349*100000000000000^3325 ≤ 12151262468273^3325*1250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249495771 1250000000 12151262468273 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366889561/2500000000 : ℝ)^4349 ≤ (45398518098301/100000000000000 : ℝ)^3325 := by
    have hnat : (1366889561 : ℕ)^4349*100000000000000^3325 ≤ 45398518098301^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366889561 2500000000 45398518098301 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596976403/5000000000 : ℝ)^4349 ≤ (8490043883197/20000000000000 : ℝ)^3325 := by
    have hnat : (2596976403 : ℕ)^4349*20000000000000^3325 ≤ 8490043883197^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596976403 5000000000 8490043883197 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249495771/1250000000 : ℝ), (1366889561/2500000000 : ℝ), (2596976403/5000000000 : ℝ)] ![(12151262468273/100000000000000 : ℝ), (45398518098301/100000000000000 : ℝ), (8490043883197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249495771/1250000000 : ℝ)|^4349 ≤ (12151262468273/100000000000000 : ℝ)^3325
        have hw : |(-249495771/1250000000 : ℝ)|=(249495771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366889561/2500000000 : ℝ)|^4349 ≤ (45398518098301/100000000000000 : ℝ)^3325
        have hw : |(1366889561/2500000000 : ℝ)|=(1366889561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596976403/5000000000 : ℝ)|^4349 ≤ (8490043883197/20000000000000 : ℝ)^3325
        have hw : |(2596976403/5000000000 : ℝ)|=(2596976403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_1 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362737501/10000000000 : ℝ)*x 0 + (-2136996369/10000000000 : ℝ)*x 1 + (5193952741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362737501/10000000000 : ℝ)^4349 ≤ (8852699607671/20000000000000 : ℝ)^3325 := by
    have hnat : (5362737501 : ℕ)^4349*20000000000000^3325 ≤ 8852699607671^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362737501 10000000000 8852699607671 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136996369/10000000000 : ℝ)^4349 ≤ (6643141612081/50000000000000 : ℝ)^3325 := by
    have hnat : (2136996369 : ℕ)^4349*50000000000000^3325 ≤ 6643141612081^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136996369 10000000000 6643141612081 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193952741/10000000000 : ℝ)^4349 ≤ (10612554680283/25000000000000 : ℝ)^3325 := by
    have hnat : (5193952741 : ℕ)^4349*25000000000000^3325 ≤ 10612554680283^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193952741 10000000000 10612554680283 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362737501/10000000000 : ℝ), (-2136996369/10000000000 : ℝ), (5193952741/10000000000 : ℝ)] ![(8852699607671/20000000000000 : ℝ), (6643141612081/50000000000000 : ℝ), (10612554680283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362737501/10000000000 : ℝ)|^4349 ≤ (8852699607671/20000000000000 : ℝ)^3325
        have hw : |(5362737501/10000000000 : ℝ)|=(5362737501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136996369/10000000000 : ℝ)|^4349 ≤ (6643141612081/50000000000000 : ℝ)^3325
        have hw : |(-2136996369/10000000000 : ℝ)|=(2136996369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193952741/10000000000 : ℝ)|^4349 ≤ (10612554680283/25000000000000 : ℝ)^3325
        have hw : |(5193952741/10000000000 : ℝ)|=(5193952741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_2 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362737339/10000000000 : ℝ)*x 0 + (324622057/625000000 : ℝ)*x 1 + (-53424909/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362737339/10000000000 : ℝ)^4349 ≤ (44263496289427/100000000000000 : ℝ)^3325 := by
    have hnat : (5362737339 : ℕ)^4349*100000000000000^3325 ≤ 44263496289427^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362737339 10000000000 44263496289427 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324622057/625000000 : ℝ)^4349 ≤ (4245022054913/10000000000000 : ℝ)^3325 := by
    have hnat : (324622057 : ℕ)^4349*10000000000000^3325 ≤ 4245022054913^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324622057 625000000 4245022054913 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53424909/250000000 : ℝ)^4349 ≤ (6643141575487/50000000000000 : ℝ)^3325 := by
    have hnat : (53424909 : ℕ)^4349*50000000000000^3325 ≤ 6643141575487^3325*250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53424909 250000000 6643141575487 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362737339/10000000000 : ℝ), (324622057/625000000 : ℝ), (-53424909/250000000 : ℝ)] ![(44263496289427/100000000000000 : ℝ), (4245022054913/10000000000000 : ℝ), (6643141575487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362737339/10000000000 : ℝ)|^4349 ≤ (44263496289427/100000000000000 : ℝ)^3325
        have hw : |(5362737339/10000000000 : ℝ)|=(5362737339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324622057/625000000 : ℝ)|^4349 ≤ (4245022054913/10000000000000 : ℝ)^3325
        have hw : |(324622057/625000000 : ℝ)|=(324622057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53424909/250000000 : ℝ)|^4349 ≤ (6643141575487/50000000000000 : ℝ)^3325
        have hw : |(-53424909/250000000 : ℝ)|=(53424909/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_3 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861869299/2000000000 : ℝ)*x 0 + (2013369561/5000000000 : ℝ)*x 1 + (2304988077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861869299/2000000000 : ℝ)^4349 ≤ (33252256826397/100000000000000 : ℝ)^3325 := by
    have hnat : (861869299 : ℕ)^4349*100000000000000^3325 ≤ 33252256826397^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861869299 2000000000 33252256826397 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013369561/5000000000 : ℝ)^4349 ≤ (15214618103401/50000000000000 : ℝ)^3325 := by
    have hnat : (2013369561 : ℕ)^4349*50000000000000^3325 ≤ 15214618103401^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013369561 5000000000 15214618103401 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2304988077/5000000000 : ℝ)^4349 ≤ (36318506945039/100000000000000 : ℝ)^3325 := by
    have hnat : (2304988077 : ℕ)^4349*100000000000000^3325 ≤ 36318506945039^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304988077 5000000000 36318506945039 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861869299/2000000000 : ℝ), (2013369561/5000000000 : ℝ), (2304988077/5000000000 : ℝ)] ![(33252256826397/100000000000000 : ℝ), (15214618103401/50000000000000 : ℝ), (36318506945039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861869299/2000000000 : ℝ)|^4349 ≤ (33252256826397/100000000000000 : ℝ)^3325
        have hw : |(861869299/2000000000 : ℝ)|=(861869299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013369561/5000000000 : ℝ)|^4349 ≤ (15214618103401/50000000000000 : ℝ)^3325
        have hw : |(2013369561/5000000000 : ℝ)|=(2013369561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2304988077/5000000000 : ℝ)|^4349 ≤ (36318506945039/100000000000000 : ℝ)^3325
        have hw : |(2304988077/5000000000 : ℝ)|=(2304988077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_4 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399203921/2000000000 : ℝ)*x 0 + (5195584019/10000000000 : ℝ)*x 1 + (1093182657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399203921/2000000000 : ℝ)^4349 ≤ (1518960997293/12500000000000 : ℝ)^3325 := by
    have hnat : (399203921 : ℕ)^4349*12500000000000^3325 ≤ 1518960997293^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399203921 2000000000 1518960997293 12500000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195584019/10000000000 : ℝ)^4349 ≤ (5308457250777/12500000000000 : ℝ)^3325 := by
    have hnat : (5195584019 : ℕ)^4349*12500000000000^3325 ≤ 5308457250777^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195584019 10000000000 5308457250777 12500000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093182657/2000000000 : ℝ)^4349 ≤ (22690327002613/50000000000000 : ℝ)^3325 := by
    have hnat : (1093182657 : ℕ)^4349*50000000000000^3325 ≤ 22690327002613^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093182657 2000000000 22690327002613 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399203921/2000000000 : ℝ), (5195584019/10000000000 : ℝ), (1093182657/2000000000 : ℝ)] ![(1518960997293/12500000000000 : ℝ), (5308457250777/12500000000000 : ℝ), (22690327002613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399203921/2000000000 : ℝ)|^4349 ≤ (1518960997293/12500000000000 : ℝ)^3325
        have hw : |(-399203921/2000000000 : ℝ)|=(399203921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195584019/10000000000 : ℝ)|^4349 ≤ (5308457250777/12500000000000 : ℝ)^3325
        have hw : |(5195584019/10000000000 : ℝ)|=(5195584019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093182657/2000000000 : ℝ)|^4349 ≤ (22690327002613/50000000000000 : ℝ)^3325
        have hw : |(1093182657/2000000000 : ℝ)|=(1093182657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_5 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291867671/10000000000 : ℝ)*x 0 + (-373007293/2000000000 : ℝ)*x 1 + (5465912971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291867671/10000000000 : ℝ)^4349 ≤ (43499959503489/100000000000000 : ℝ)^3325 := by
    have hnat : (5291867671 : ℕ)^4349*100000000000000^3325 ≤ 43499959503489^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291867671 10000000000 43499959503489 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373007293/2000000000 : ℝ)^4349 ≤ (5559694945111/50000000000000 : ℝ)^3325 := by
    have hnat : (373007293 : ℕ)^4349*50000000000000^3325 ≤ 5559694945111^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373007293 2000000000 5559694945111 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465912971/10000000000 : ℝ)^4349 ≤ (363045204763/800000000000 : ℝ)^3325 := by
    have hnat : (5465912971 : ℕ)^4349*800000000000^3325 ≤ 363045204763^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465912971 10000000000 363045204763 800000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291867671/10000000000 : ℝ), (-373007293/2000000000 : ℝ), (5465912971/10000000000 : ℝ)] ![(43499959503489/100000000000000 : ℝ), (5559694945111/50000000000000 : ℝ), (363045204763/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291867671/10000000000 : ℝ)|^4349 ≤ (43499959503489/100000000000000 : ℝ)^3325
        have hw : |(5291867671/10000000000 : ℝ)|=(5291867671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373007293/2000000000 : ℝ)|^4349 ≤ (5559694945111/50000000000000 : ℝ)^3325
        have hw : |(-373007293/2000000000 : ℝ)|=(373007293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465912971/10000000000 : ℝ)|^4349 ≤ (363045204763/800000000000 : ℝ)^3325
        have hw : |(5465912971/10000000000 : ℝ)|=(5465912971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_6 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322967279/2500000000 : ℝ)*x 0 + (2732956497/5000000000 : ℝ)*x 1 + (-46625861/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322967279/2500000000 : ℝ)^4349 ≤ (21749987519857/50000000000000 : ℝ)^3325 := by
    have hnat : (1322967279 : ℕ)^4349*50000000000000^3325 ≤ 21749987519857^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322967279 2500000000 21749987519857 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732956497/5000000000 : ℝ)^4349 ≤ (45380650845141/100000000000000 : ℝ)^3325 := by
    have hnat : (2732956497 : ℕ)^4349*100000000000000^3325 ≤ 45380650845141^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732956497 5000000000 45380650845141 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46625861/250000000 : ℝ)^4349 ≤ (5559687049489/50000000000000 : ℝ)^3325 := by
    have hnat : (46625861 : ℕ)^4349*50000000000000^3325 ≤ 5559687049489^3325*250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46625861 250000000 5559687049489 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322967279/2500000000 : ℝ), (2732956497/5000000000 : ℝ), (-46625861/250000000 : ℝ)] ![(21749987519857/50000000000000 : ℝ), (45380650845141/100000000000000 : ℝ), (5559687049489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322967279/2500000000 : ℝ)|^4349 ≤ (21749987519857/50000000000000 : ℝ)^3325
        have hw : |(1322967279/2500000000 : ℝ)|=(1322967279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732956497/5000000000 : ℝ)|^4349 ≤ (45380650845141/100000000000000 : ℝ)^3325
        have hw : |(2732956497/5000000000 : ℝ)|=(2732956497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46625861/250000000 : ℝ)|^4349 ≤ (5559687049489/50000000000000 : ℝ)^3325
        have hw : |(-46625861/250000000 : ℝ)|=(46625861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s2_7 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077365463/2500000000 : ℝ)*x 0 + (4606499469/10000000000 : ℝ)*x 1 + (2015122507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077365463/2500000000 : ℝ)^4349 ≤ (33253421095071/100000000000000 : ℝ)^3325 := by
    have hnat : (1077365463 : ℕ)^4349*100000000000000^3325 ≤ 33253421095071^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077365463 2500000000 33253421095071 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4606499469/10000000000 : ℝ)^4349 ≤ (36282685593899/100000000000000 : ℝ)^3325 := by
    have hnat : (4606499469 : ℕ)^4349*100000000000000^3325 ≤ 36282685593899^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606499469 10000000000 36282685593899 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015122507/5000000000 : ℝ)^4349 ≤ (30463893293907/100000000000000 : ℝ)^3325 := by
    have hnat : (2015122507 : ℕ)^4349*100000000000000^3325 ≤ 30463893293907^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015122507 5000000000 30463893293907 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077365463/2500000000 : ℝ), (4606499469/10000000000 : ℝ), (2015122507/5000000000 : ℝ)] ![(33253421095071/100000000000000 : ℝ), (36282685593899/100000000000000 : ℝ), (30463893293907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077365463/2500000000 : ℝ)|^4349 ≤ (33253421095071/100000000000000 : ℝ)^3325
        have hw : |(1077365463/2500000000 : ℝ)|=(1077365463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4606499469/10000000000 : ℝ)|^4349 ≤ (36282685593899/100000000000000 : ℝ)^3325
        have hw : |(4606499469/10000000000 : ℝ)|=(4606499469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015122507/5000000000 : ℝ)|^4349 ≤ (30463893293907/100000000000000 : ℝ)^3325
        have hw : |(2015122507/5000000000 : ℝ)|=(2015122507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1389_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (239/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1593/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (239/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (239/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (239/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (239/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (239/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (239/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (7313/100000 : ℝ) ^ (1087/256 : ℝ) ≤ (1502599755095683/100000000000000000000 : ℝ) := by
    have hpowers : (7313/100000 : ℝ)^1087 ≤ (1502599755095683/100000000000000000000 : ℝ)^256 := by
      have hnat : (7313 : ℕ)^1087*100000000000000000000^256 ≤ 1502599755095683^256*100000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7313 100000 1502599755095683 100000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7313/100000 : ℝ)) (X := (1502599755095683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hpowhi : (239/1250 : ℝ) ^ (1087/256 : ℝ) ≤ (44473388060142191/50000000000000000000 : ℝ) := by
    have hpowers : (239/1250 : ℝ)^1087 ≤ (44473388060142191/50000000000000000000 : ℝ)^256 := by
      have hnat : (239 : ℕ)^1087*50000000000000000000^256 ≤ 44473388060142191^256*1250^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        239 1250 44473388060142191 50000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (239/1250 : ℝ)) (X := (44473388060142191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001502599755095683/50000000000000000000 : ℝ) ≤ (10000070774814839/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (50001502599755095683/50000000000000000000 : ℝ)^256 ≤ (10000070774814839/10000000000000000 : ℝ)^1087 := by
      have hnat : (50001502599755095683 : ℕ)^256*10000000000000000^1087 ≤ 10000070774814839^1087*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001502599755095683 50000000000000000000 10000070774814839 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000070774814839/10000000000000000 : ℝ)) (X := (50001502599755095683/50000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20018089875175076013/20000000000000000000 : ℝ) ≤ (10002129442401479/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (20018089875175076013/20000000000000000000 : ℝ)^256 ≤ (10002129442401479/10000000000000000 : ℝ)^1087 := by
      have hnat : (20018089875175076013 : ℕ)^256*10000000000000000^1087 ≤ 10002129442401479^1087*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20018089875175076013 20000000000000000000 10002129442401479 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002129442401479/10000000000000000 : ℝ)) (X := (20018089875175076013/20000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25044473388060142191/25000000000000000000 : ℝ) ≤ (10004188109988119/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (25044473388060142191/25000000000000000000 : ℝ)^256 ≤ (10004188109988119/10000000000000000 : ℝ)^1087 := by
      have hnat : (25044473388060142191 : ℕ)^256*10000000000000000^1087 ≤ 10004188109988119^1087*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044473388060142191 25000000000000000000 10004188109988119 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004188109988119/10000000000000000 : ℝ)) (X := (25044473388060142191/25000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1502599755095683/100000000000000000000 : ℝ) ≤ ((118040725566116607433/118070000000000000000 : ℝ)+2*(25733344833/14758750000000 : ℝ)*(7313/100000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (118040725566116607433/118070000000000000000 : ℝ)+2*(25733344833/14758750000000 : ℝ)*(7313/100000 : ℝ)=(10000070774814839/10000000000000000 : ℝ) by norm_num, show 1+2*(1502599755095683/100000000000000000000 : ℝ)=(50001502599755095683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44473388060142191/50000000000000000000 : ℝ)+(1502599755095683/100000000000000000000 : ℝ) ≤ ((118040725566116607433/118070000000000000000 : ℝ)+(25733344833/14758750000000 : ℝ)*((239/1250 : ℝ)+(7313/100000 : ℝ)))^(1087/256 : ℝ) := by
    rw [show (118040725566116607433/118070000000000000000 : ℝ)+(25733344833/14758750000000 : ℝ)*((239/1250 : ℝ)+(7313/100000 : ℝ))=(10002129442401479/10000000000000000 : ℝ) by norm_num, show 1+(44473388060142191/50000000000000000000 : ℝ)+(1502599755095683/100000000000000000000 : ℝ)=(20018089875175076013/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44473388060142191/50000000000000000000 : ℝ) ≤ ((118040725566116607433/118070000000000000000 : ℝ)+2*(25733344833/14758750000000 : ℝ)*(239/1250 : ℝ))^(1087/256 : ℝ) := by
    rw [show (118040725566116607433/118070000000000000000 : ℝ)+2*(25733344833/14758750000000 : ℝ)*(239/1250 : ℝ)=(10004188109988119/10000000000000000 : ℝ) by norm_num, show 1+2*(44473388060142191/50000000000000000000 : ℝ)=(25044473388060142191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (118040725566116607433/118070000000000000000 : ℝ)*(X 1 0+X 2 0)+(25733344833/14758750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (7313/100000 : ℝ)) (hi := (239/1250 : ℝ)) (c := (118040725566116607433/118070000000000000000 : ℝ)) (alpha := (25733344833/14758750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (118040725566116607433/118070000000000000000 : ℝ)*(X 0 1+X 2 1)+(25733344833/14758750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (7313/100000 : ℝ)) (hi := (239/1250 : ℝ)) (c := (118040725566116607433/118070000000000000000 : ℝ)) (alpha := (25733344833/14758750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (118040725566116607433/118070000000000000000 : ℝ)*(X 0 2+X 1 2)+(25733344833/14758750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (7313/100000 : ℝ)) (hi := (239/1250 : ℝ)) (c := (118040725566116607433/118070000000000000000 : ℝ)) (alpha := (25733344833/14758750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-249495771/1250000000 : ℝ)*X 0 0+(1366889561/2500000000 : ℝ)*X 0 1+(2596976403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362737501/10000000000 : ℝ)*X 1 0+(-2136996369/10000000000 : ℝ)*X 1 1+(5193952741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362737339/10000000000 : ℝ)*X 2 0+(324622057/625000000 : ℝ)*X 2 1+(-53424909/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861869299/2000000000 : ℝ)*X 0 0+(2013369561/5000000000 : ℝ)*X 0 1+(2304988077/5000000000 : ℝ)*X 0 2+(861869299/2000000000 : ℝ)*X 1 0+(2013369561/5000000000 : ℝ)*X 1 1+(2304988077/5000000000 : ℝ)*X 1 2+(861869299/2000000000 : ℝ)*X 2 0+(2013369561/5000000000 : ℝ)*X 2 1+(2304988077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-399203921/2000000000 : ℝ)*X 0 0+(5195584019/10000000000 : ℝ)*X 0 1+(1093182657/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291867671/10000000000 : ℝ)*X 1 0+(-373007293/2000000000 : ℝ)*X 1 1+(5465912971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322967279/2500000000 : ℝ)*X 2 0+(2732956497/5000000000 : ℝ)*X 2 1+(-46625861/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077365463/2500000000 : ℝ)*X 0 0+(4606499469/10000000000 : ℝ)*X 0 1+(2015122507/5000000000 : ℝ)*X 0 2+(1077365463/2500000000 : ℝ)*X 1 0+(4606499469/10000000000 : ℝ)*X 1 1+(2015122507/5000000000 : ℝ)*X 1 2+(1077365463/2500000000 : ℝ)*X 2 0+(4606499469/10000000000 : ℝ)*X 2 1+(2015122507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59160435364053662188995218949/5903500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116644153/6250000000000 : ℝ)*(base19) + (63327381/4000000000000 : ℝ)*(base23) + (11577601/12500000000000 : ℝ)*(lower2) + (302518691/100000000000000 : ℝ)*(upper3) + (149192177/100000000000000 : ℝ)*(upper5) + (2684766975191649/100000000000000 : ℝ)*(major0) + (2684766975191649/100000000000000 : ℝ)*(major1) + (2684766975191649/100000000000000 : ℝ)*(major2) + (1827460882068219/50000000000000 : ℝ)*(sp0) + (913735220439207/25000000000000 : ℝ)*(sp1) + (3654941164878751/100000000000000 : ℝ)*(sp2) + (857289461590789/50000000000000 : ℝ)*(sp3) + (20983926837/100000000000000 : ℝ)*(sp4) + (238901937/2000000000000 : ℝ)*(sp7) + (1714590868278429/100000000000000 : ℝ)*(f.failure) + (913735687015819/25000000000000 : ℝ)*(f.sum) + (4022473721137/2361400000000000000000000000 : ℝ)*base65 + (11000620840421927017/11807000000000000000000000000000000 : ℝ)*base67 + (22316549480413927017/11807000000000000000000000000000000 : ℝ)*base69 + (73905221080442927017/11807000000000000000000000000000000 : ℝ)*base71 + (2131660672617/5903500000000000000000000000 : ℝ)*base73 + (113969183561411072983/11807000000000000000000000000000000 : ℝ)*base76 + (13489076463315927017/11807000000000000000000000000000000 : ℝ)*base77 + (54802861597137072983/11807000000000000000000000000000000 : ℝ)*base80 + (10304032803301/1475875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4394043/5000000000000000000000 : ℝ)*base89 + (4394043/5000000000000000000000 : ℝ)*base91 + (4394043/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9171413688010888342400083431/1475875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (929813579/100000000000000 : ℝ)*(base19) + (1552923399/50000000000000 : ℝ)*(base23) + (121510629/50000000000000 : ℝ)*(upper3) + (159335507/50000000000000 : ℝ)*(lower4) + (8317793/20000000000000 : ℝ)*(upper5) + (1358634747509731/50000000000000 : ℝ)*(major0) + (1358634747509731/50000000000000 : ℝ)*(major1) + (1358634747509731/50000000000000 : ℝ)*(major2) + (143425671/6250000000000 : ℝ)*(sp1) + (44390510501/100000000000000 : ℝ)*(sp2) + (3699190610835963/100000000000000 : ℝ)*(sp4) + (57799802909557/1562500000000 : ℝ)*(sp5) + (462392889309833/12500000000000 : ℝ)*(sp6) + (1735348172062243/100000000000000 : ℝ)*(sp7) + (1735348172062243/100000000000000 : ℝ)*(f.failure) + (3699190610835963/100000000000000 : ℝ)*(f.sum) + (9487744073789/11807000000000000000000000000 : ℝ)*base65 + (29734778825734430523/5903500000000000000000000000000000 : ℝ)*base67 + (87516167099958930523/5903500000000000000000000000000000 : ℝ)*base69 + (5248018041771569477/5903500000000000000000000000000000 : ℝ)*base72 + (1610667896939/2361400000000000000000000000 : ℝ)*base73 + (84207579280907430523/5903500000000000000000000000000000 : ℝ)*base75 + (38512293692511930523/5903500000000000000000000000000000 : ℝ)*base77 + (69077983755125930523/5903500000000000000000000000000000 : ℝ)*base79 + (16707654468381/5903500000000000000000000000 : ℝ)*base81 + (61546619/5000000000000000000000 : ℝ)*base90 + (61546619/5000000000000000000000 : ℝ)*base92 + (61546619/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1389_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (239/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1389_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1389_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1389_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1389_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1389_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1389_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
