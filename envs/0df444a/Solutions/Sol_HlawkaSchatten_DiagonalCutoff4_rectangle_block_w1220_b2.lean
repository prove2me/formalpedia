-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1220_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:10:36.008336+00:00
-- url     : https://prove2.me/submissions/e95e23a1-a333-4120-8d30-da8bddd1acdd

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
theorem support_rectangle_w1220_s6_0 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-133132099/625000000 : ℝ)*x 0 + (1078365223/2000000000 : ℝ)*x 1 + (658338427/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133132099/625000000 : ℝ)^8413 ≤ (6475598177733/50000000000000 : ℝ)^6365 := by
    have hnat : (133132099 : ℕ)^8413*50000000000000^6365 ≤ 6475598177733^6365*625000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133132099 625000000 6475598177733 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078365223/2000000000 : ℝ)^8413 ≤ (11049924833201/25000000000000 : ℝ)^6365 := by
    have hnat : (1078365223 : ℕ)^8413*25000000000000^6365 ≤ 11049924833201^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078365223 2000000000 11049924833201 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658338427/1250000000 : ℝ)^8413 ≤ (8569820859417/20000000000000 : ℝ)^6365 := by
    have hnat : (658338427 : ℕ)^8413*20000000000000^6365 ≤ 8569820859417^6365*1250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658338427 1250000000 8569820859417 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133132099/625000000 : ℝ), (1078365223/2000000000 : ℝ), (658338427/1250000000 : ℝ)] ![(6475598177733/50000000000000 : ℝ), (11049924833201/25000000000000 : ℝ), (8569820859417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133132099/625000000 : ℝ)|^8413 ≤ (6475598177733/50000000000000 : ℝ)^6365
        have hw : |(-133132099/625000000 : ℝ)|=(133132099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078365223/2000000000 : ℝ)|^8413 ≤ (11049924833201/25000000000000 : ℝ)^6365
        have hw : |(1078365223/2000000000 : ℝ)|=(1078365223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658338427/1250000000 : ℝ)|^8413 ≤ (8569820859417/20000000000000 : ℝ)^6365
        have hw : |(658338427/1250000000 : ℝ)|=(658338427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_1 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344477321/10000000000 : ℝ)*x 0 + (-2193560203/10000000000 : ℝ)*x 1 + (2633353663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344477321/10000000000 : ℝ)^8413 ≤ (43687393124229/100000000000000 : ℝ)^6365 := by
    have hnat : (5344477321 : ℕ)^8413*100000000000000^6365 ≤ 43687393124229^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344477321 10000000000 43687393124229 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193560203/10000000000 : ℝ)^8413 ≤ (13463503530313/100000000000000 : ℝ)^6365 := by
    have hnat : (2193560203 : ℕ)^8413*100000000000000^6365 ≤ 13463503530313^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193560203 10000000000 13463503530313 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633353663/5000000000 : ℝ)^8413 ≤ (42849103329259/100000000000000 : ℝ)^6365 := by
    have hnat : (2633353663 : ℕ)^8413*100000000000000^6365 ≤ 42849103329259^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633353663 5000000000 42849103329259 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344477321/10000000000 : ℝ), (-2193560203/10000000000 : ℝ), (2633353663/5000000000 : ℝ)] ![(43687393124229/100000000000000 : ℝ), (13463503530313/100000000000000 : ℝ), (42849103329259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344477321/10000000000 : ℝ)|^8413 ≤ (43687393124229/100000000000000 : ℝ)^6365
        have hw : |(5344477321/10000000000 : ℝ)|=(5344477321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193560203/10000000000 : ℝ)|^8413 ≤ (13463503530313/100000000000000 : ℝ)^6365
        have hw : |(-2193560203/10000000000 : ℝ)|=(2193560203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633353663/5000000000 : ℝ)|^8413 ≤ (42849103329259/100000000000000 : ℝ)^6365
        have hw : |(2633353663/5000000000 : ℝ)|=(2633353663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_2 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344477269/10000000000 : ℝ)*x 0 + (2633353679/5000000000 : ℝ)*x 1 + (-2193560229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344477269/10000000000 : ℝ)^8413 ≤ (10921848140599/25000000000000 : ℝ)^6365 := by
    have hnat : (5344477269 : ℕ)^8413*25000000000000^6365 ≤ 10921848140599^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344477269 10000000000 10921848140599 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633353679/5000000000 : ℝ)^8413 ≤ (342792829387/800000000000 : ℝ)^6365 := by
    have hnat : (2633353679 : ℕ)^8413*800000000000^6365 ≤ 342792829387^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633353679 5000000000 342792829387 800000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193560229/10000000000 : ℝ)^8413 ≤ (13463503741241/100000000000000 : ℝ)^6365 := by
    have hnat : (2193560229 : ℕ)^8413*100000000000000^6365 ≤ 13463503741241^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193560229 10000000000 13463503741241 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344477269/10000000000 : ℝ), (2633353679/5000000000 : ℝ), (-2193560229/10000000000 : ℝ)] ![(10921848140599/25000000000000 : ℝ), (342792829387/800000000000 : ℝ), (13463503741241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344477269/10000000000 : ℝ)|^8413 ≤ (10921848140599/25000000000000 : ℝ)^6365
        have hw : |(5344477269/10000000000 : ℝ)|=(5344477269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633353679/5000000000 : ℝ)|^8413 ≤ (342792829387/800000000000 : ℝ)^6365
        have hw : |(2633353679/5000000000 : ℝ)|=(2633353679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193560229/10000000000 : ℝ)|^8413 ≤ (13463503741241/100000000000000 : ℝ)^6365
        have hw : |(-2193560229/10000000000 : ℝ)|=(2193560229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_3 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353788361/10000000000 : ℝ)*x 0 + (4229213317/10000000000 : ℝ)*x 1 + (4481947851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353788361/10000000000 : ℝ)^8413 ≤ (416465864293/1250000000000 : ℝ)^6365 := by
    have hnat : (4353788361 : ℕ)^8413*1250000000000^6365 ≤ 416465864293^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353788361 10000000000 416465864293 1250000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229213317/10000000000 : ℝ)^8413 ≤ (8015765927651/25000000000000 : ℝ)^6365 := by
    have hnat : (4229213317 : ℕ)^8413*25000000000000^6365 ≤ 8015765927651^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229213317 10000000000 8015765927651 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481947851/10000000000 : ℝ)^8413 ≤ (17309833563179/50000000000000 : ℝ)^6365 := by
    have hnat : (4481947851 : ℕ)^8413*50000000000000^6365 ≤ 17309833563179^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481947851 10000000000 17309833563179 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353788361/10000000000 : ℝ), (4229213317/10000000000 : ℝ), (4481947851/10000000000 : ℝ)] ![(416465864293/1250000000000 : ℝ), (8015765927651/25000000000000 : ℝ), (17309833563179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353788361/10000000000 : ℝ)|^8413 ≤ (416465864293/1250000000000 : ℝ)^6365
        have hw : |(4353788361/10000000000 : ℝ)|=(4353788361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229213317/10000000000 : ℝ)|^8413 ≤ (8015765927651/25000000000000 : ℝ)^6365
        have hw : |(4229213317/10000000000 : ℝ)|=(4229213317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481947851/10000000000 : ℝ)|^8413 ≤ (17309833563179/50000000000000 : ℝ)^6365
        have hw : |(4481947851/10000000000 : ℝ)|=(4481947851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_4 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065059191/5000000000 : ℝ)*x 0 + (5267023691/10000000000 : ℝ)*x 1 + (336969291/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065059191/5000000000 : ℝ)^8413 ≤ (2590246982791/20000000000000 : ℝ)^6365 := by
    have hnat : (1065059191 : ℕ)^8413*20000000000000^6365 ≤ 2590246982791^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065059191 5000000000 2590246982791 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267023691/10000000000 : ℝ)^8413 ≤ (167392599351/390625000000 : ℝ)^6365 := by
    have hnat : (5267023691 : ℕ)^8413*390625000000^6365 ≤ 167392599351^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267023691 10000000000 167392599351 390625000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336969291/625000000 : ℝ)^8413 ≤ (44196259641661/100000000000000 : ℝ)^6365 := by
    have hnat : (336969291 : ℕ)^8413*100000000000000^6365 ≤ 44196259641661^6365*625000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336969291 625000000 44196259641661 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065059191/5000000000 : ℝ), (5267023691/10000000000 : ℝ), (336969291/625000000 : ℝ)] ![(2590246982791/20000000000000 : ℝ), (167392599351/390625000000 : ℝ), (44196259641661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065059191/5000000000 : ℝ)|^8413 ≤ (2590246982791/20000000000000 : ℝ)^6365
        have hw : |(-1065059191/5000000000 : ℝ)|=(1065059191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267023691/10000000000 : ℝ)|^8413 ≤ (167392599351/390625000000 : ℝ)^6365
        have hw : |(5267023691/10000000000 : ℝ)|=(5267023691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336969291/625000000 : ℝ)|^8413 ≤ (44196259641661/100000000000000 : ℝ)^6365
        have hw : |(336969291/625000000 : ℝ)|=(336969291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_5 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328150139/2500000000 : ℝ)*x 0 + (-1034379447/5000000000 : ℝ)*x 1 + (539150867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328150139/2500000000 : ℝ)^8413 ≤ (5417914072171/12500000000000 : ℝ)^6365 := by
    have hnat : (1328150139 : ℕ)^8413*12500000000000^6365 ≤ 5417914072171^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328150139 2500000000 5417914072171 12500000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034379447/5000000000 : ℝ)^8413 ≤ (3115106904143/25000000000000 : ℝ)^6365 := by
    have hnat : (1034379447 : ℕ)^8413*25000000000000^6365 ≤ 3115106904143^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034379447 5000000000 3115106904143 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539150867/1000000000 : ℝ)^8413 ≤ (883925195867/2000000000000 : ℝ)^6365 := by
    have hnat : (539150867 : ℕ)^8413*2000000000000^6365 ≤ 883925195867^6365*1000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539150867 1000000000 883925195867 2000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328150139/2500000000 : ℝ), (-1034379447/5000000000 : ℝ), (539150867/1000000000 : ℝ)] ![(5417914072171/12500000000000 : ℝ), (3115106904143/25000000000000 : ℝ), (883925195867/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328150139/2500000000 : ℝ)|^8413 ≤ (5417914072171/12500000000000 : ℝ)^6365
        have hw : |(1328150139/2500000000 : ℝ)|=(1328150139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034379447/5000000000 : ℝ)|^8413 ≤ (3115106904143/25000000000000 : ℝ)^6365
        have hw : |(-1034379447/5000000000 : ℝ)|=(1034379447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539150867/1000000000 : ℝ)|^8413 ≤ (883925195867/2000000000000 : ℝ)^6365
        have hw : |(539150867/1000000000 : ℝ)|=(539150867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_6 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328150143/2500000000 : ℝ)*x 0 + (1078301731/2000000000 : ℝ)*x 1 + (-517189723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328150143/2500000000 : ℝ)^8413 ≤ (10835828187477/25000000000000 : ℝ)^6365 := by
    have hnat : (1328150143 : ℕ)^8413*25000000000000^6365 ≤ 10835828187477^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328150143 2500000000 10835828187477 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078301731/2000000000 : ℝ)^8413 ≤ (22098129815413/50000000000000 : ℝ)^6365 := by
    have hnat : (1078301731 : ℕ)^8413*50000000000000^6365 ≤ 22098129815413^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078301731 2000000000 22098129815413 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517189723/2500000000 : ℝ)^8413 ≤ (12460427600649/100000000000000 : ℝ)^6365 := by
    have hnat : (517189723 : ℕ)^8413*100000000000000^6365 ≤ 12460427600649^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517189723 2500000000 12460427600649 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328150143/2500000000 : ℝ), (1078301731/2000000000 : ℝ), (-517189723/2500000000 : ℝ)] ![(10835828187477/25000000000000 : ℝ), (22098129815413/50000000000000 : ℝ), (12460427600649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328150143/2500000000 : ℝ)|^8413 ≤ (10835828187477/25000000000000 : ℝ)^6365
        have hw : |(1328150143/2500000000 : ℝ)|=(1328150143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078301731/2000000000 : ℝ)|^8413 ≤ (22098129815413/50000000000000 : ℝ)^6365
        have hw : |(1078301731/2000000000 : ℝ)|=(1078301731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517189723/2500000000 : ℝ)|^8413 ≤ (12460427600649/100000000000000 : ℝ)^6365
        have hw : |(-517189723/2500000000 : ℝ)|=(517189723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s6_7 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353798051/10000000000 : ℝ)*x 0 + (140040901/312500000 : ℝ)*x 1 + (4229854571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353798051/10000000000 : ℝ)^8413 ≤ (3331736715527/10000000000000 : ℝ)^6365 := by
    have hnat : (4353798051 : ℕ)^8413*10000000000000^6365 ≤ 3331736715527^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353798051 10000000000 3331736715527 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140040901/312500000 : ℝ)^8413 ≤ (34613143149997/100000000000000 : ℝ)^6365 := by
    have hnat : (140040901 : ℕ)^8413*100000000000000^6365 ≤ 34613143149997^6365*312500000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140040901 312500000 34613143149997 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229854571/10000000000 : ℝ)^8413 ≤ (16034744839523/50000000000000 : ℝ)^6365 := by
    have hnat : (4229854571 : ℕ)^8413*50000000000000^6365 ≤ 16034744839523^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229854571 10000000000 16034744839523 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353798051/10000000000 : ℝ), (140040901/312500000 : ℝ), (4229854571/10000000000 : ℝ)] ![(3331736715527/10000000000000 : ℝ), (34613143149997/100000000000000 : ℝ), (16034744839523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353798051/10000000000 : ℝ)|^8413 ≤ (3331736715527/10000000000000 : ℝ)^6365
        have hw : |(4353798051/10000000000 : ℝ)|=(4353798051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140040901/312500000 : ℝ)|^8413 ≤ (34613143149997/100000000000000 : ℝ)^6365
        have hw : |(140040901/312500000 : ℝ)|=(140040901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229854571/10000000000 : ℝ)|^8413 ≤ (16034744839523/50000000000000 : ℝ)^6365
        have hw : |(4229854571/10000000000 : ℝ)|=(4229854571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1220_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11447/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7049/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (457/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (457/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (457/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (457/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (457/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (457/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (457/4000 : ℝ) ^ (2103/512 : ℝ) ≤ (2699280256084689/20000000000000000000 : ℝ) := by
    have hpowers : (457/4000 : ℝ)^2103 ≤ (2699280256084689/20000000000000000000 : ℝ)^512 := by
      have hnat : (457 : ℕ)^2103*20000000000000000000^512 ≤ 2699280256084689^512*4000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        457 4000 2699280256084689 20000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (457/4000 : ℝ)) (X := (2699280256084689/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (2103/512 : ℝ) ≤ (1288839258555003/4000000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^2103 ≤ (1288839258555003/4000000000000000000 : ℝ)^512 := by
      have hnat : (14121 : ℕ)^2103*4000000000000000000^512 ≤ 1288839258555003^512*100000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 1288839258555003 4000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (1288839258555003/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002699280256084689/10000000000000000000 : ℝ) ≤ (10000657104327379/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (10002699280256084689/10000000000000000000 : ℝ)^512 ≤ (10000657104327379/10000000000000000 : ℝ)^2103 := by
      have hnat : (10002699280256084689 : ℕ)^512*10000000000000000^2103 ≤ 10000657104327379^2103*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002699280256084689 10000000000000000000 10000657104327379 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000657104327379/10000000000000000 : ℝ)) (X := (10002699280256084689/10000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501142934568607463/2500000000000000000 : ℝ) ≤ (2000222570167501/2000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (2501142934568607463/2500000000000000000 : ℝ)^512 ≤ (2000222570167501/2000000000000000 : ℝ)^2103 := by
      have hnat : (2501142934568607463 : ℕ)^512*2000000000000000^2103 ≤ 2000222570167501^2103*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501142934568607463 2500000000000000000 2000222570167501 2000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222570167501/2000000000000000 : ℝ)) (X := (2501142934568607463/2500000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001288839258555003/2000000000000000000 : ℝ) ≤ (10001568597347631/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (2001288839258555003/2000000000000000000 : ℝ)^512 ≤ (10001568597347631/10000000000000000 : ℝ)^2103 := by
      have hnat : (2001288839258555003 : ℕ)^512*10000000000000000^2103 ≤ 10001568597347631^2103*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001288839258555003 2000000000000000000 10001568597347631 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001568597347631/10000000000000000 : ℝ)) (X := (2001288839258555003/2000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2699280256084689/20000000000000000000 : ℝ) ≤ ((6737839436377558671/6740000000000000000 : ℝ)+2*(227873255063/134800000000000 : ℝ)*(457/4000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (6737839436377558671/6740000000000000000 : ℝ)+2*(227873255063/134800000000000 : ℝ)*(457/4000 : ℝ)=(10000657104327379/10000000000000000 : ℝ) by norm_num, show 1+2*(2699280256084689/20000000000000000000 : ℝ)=(10002699280256084689/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1288839258555003/4000000000000000000 : ℝ)+(2699280256084689/20000000000000000000 : ℝ) ≤ ((6737839436377558671/6740000000000000000 : ℝ)+(227873255063/134800000000000 : ℝ)*((14121/100000 : ℝ)+(457/4000 : ℝ)))^(2103/512 : ℝ) := by
    rw [show (6737839436377558671/6740000000000000000 : ℝ)+(227873255063/134800000000000 : ℝ)*((14121/100000 : ℝ)+(457/4000 : ℝ))=(2000222570167501/2000000000000000 : ℝ) by norm_num, show 1+(1288839258555003/4000000000000000000 : ℝ)+(2699280256084689/20000000000000000000 : ℝ)=(2501142934568607463/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1288839258555003/4000000000000000000 : ℝ) ≤ ((6737839436377558671/6740000000000000000 : ℝ)+2*(227873255063/134800000000000 : ℝ)*(14121/100000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (6737839436377558671/6740000000000000000 : ℝ)+2*(227873255063/134800000000000 : ℝ)*(14121/100000 : ℝ)=(10001568597347631/10000000000000000 : ℝ) by norm_num, show 1+2*(1288839258555003/4000000000000000000 : ℝ)=(2001288839258555003/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6737839436377558671/6740000000000000000 : ℝ)*(X 1 0+X 2 0)+(227873255063/134800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (6737839436377558671/6740000000000000000 : ℝ)) (alpha := (227873255063/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6737839436377558671/6740000000000000000 : ℝ)*(X 0 1+X 2 1)+(227873255063/134800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (6737839436377558671/6740000000000000000 : ℝ)) (alpha := (227873255063/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6737839436377558671/6740000000000000000 : ℝ)*(X 0 2+X 1 2)+(227873255063/134800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (6737839436377558671/6740000000000000000 : ℝ)) (alpha := (227873255063/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-133132099/625000000 : ℝ)*X 0 0+(1078365223/2000000000 : ℝ)*X 0 1+(658338427/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344477321/10000000000 : ℝ)*X 1 0+(-2193560203/10000000000 : ℝ)*X 1 1+(2633353663/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344477269/10000000000 : ℝ)*X 2 0+(2633353679/5000000000 : ℝ)*X 2 1+(-2193560229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353788361/10000000000 : ℝ)*X 0 0+(4229213317/10000000000 : ℝ)*X 0 1+(4481947851/10000000000 : ℝ)*X 0 2+(4353788361/10000000000 : ℝ)*X 1 0+(4229213317/10000000000 : ℝ)*X 1 1+(4481947851/10000000000 : ℝ)*X 1 2+(4353788361/10000000000 : ℝ)*X 2 0+(4229213317/10000000000 : ℝ)*X 2 1+(4481947851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065059191/5000000000 : ℝ)*X 0 0+(5267023691/10000000000 : ℝ)*X 0 1+(336969291/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328150139/2500000000 : ℝ)*X 1 0+(-1034379447/5000000000 : ℝ)*X 1 1+(539150867/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328150143/2500000000 : ℝ)*X 2 0+(1078301731/2000000000 : ℝ)*X 2 1+(-517189723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353798051/10000000000 : ℝ)*X 0 0+(140040901/312500000 : ℝ)*X 0 1+(4229854571/10000000000 : ℝ)*X 0 2+(4353798051/10000000000 : ℝ)*X 1 0+(140040901/312500000 : ℝ)*X 1 1+(4229854571/10000000000 : ℝ)*X 1 2+(4353798051/10000000000 : ℝ)*X 2 0+(140040901/312500000 : ℝ)*X 2 1+(4229854571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540664908821326143326503047/67400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1425201897/100000000000000 : ℝ)*(base19) + (623342749/50000000000000 : ℝ)*(base23) + (53846783/100000000000000 : ℝ)*(lower2) + (47128877/25000000000000 : ℝ)*(upper3) + (57274811/100000000000000 : ℝ)*(upper5) + (1194924199072381/20000000000000 : ℝ)*(major0) + (1194924199072381/20000000000000 : ℝ)*(major1) + (1194924199072381/20000000000000 : ℝ)*(major2) + (3996224633537397/50000000000000 : ℝ)*(sp0) + (7992481025991829/100000000000000 : ℝ)*(sp1) + (1998120301127057/25000000000000 : ℝ)*(sp2) + (1978369298860157/50000000000000 : ℝ)*(sp3) + (8296029733/25000000000000 : ℝ)*(sp4) + (20674418611/100000000000000 : ℝ)*(sp7) + (989189818034731/25000000000000 : ℝ)*(f.failure) + (3996241225596863/50000000000000 : ℝ)*(f.sum) + (3490553892657/1348000000000000000000000000 : ℝ)*base66 + (364475177175715651/134800000000000000000000000000000 : ℝ)*base67 + (1134377750326515651/134800000000000000000000000000000 : ℝ)*base69 + (949116504361884349/134800000000000000000000000000000 : ℝ)*base72 + (7354636073841/1348000000000000000000000000 : ℝ)*base74 + (269973888308115651/134800000000000000000000000000000 : ℝ)*base75 + (38900967622284349/134800000000000000000000000000000 : ℝ)*base78 + (1250639822066115651/134800000000000000000000000000000 : ℝ)*base79 + (947710376719/1348000000000000000000000000 : ℝ)*base81 + (17053691/2500000000000000000000 : ℝ)*base90 + (17053691/2500000000000000000000 : ℝ)*base92 + (17053691/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3317760800240256779504905527/337000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880747293/50000000000000 : ℝ)*(base19) + (241699339/12500000000000 : ℝ)*(base23) + (3928487/2000000000000 : ℝ)*(upper3) + (4129737/6250000000000 : ℝ)*(lower4) + (195298817/100000000000000 : ℝ)*(upper5) + (6004981676553807/100000000000000 : ℝ)*(major0) + (6004981676553807/100000000000000 : ℝ)*(major1) + (6004981676553807/100000000000000 : ℝ)*(major2) + (50208212573/100000000000000 : ℝ)*(sp1) + (54130048879/100000000000000 : ℝ)*(sp2) + (8033097053664893/100000000000000 : ℝ)*(sp4) + (4016522541978867/50000000000000 : ℝ)*(sp5) + (8033040990021303/100000000000000 : ℝ)*(sp6) + (1988432985638227/50000000000000 : ℝ)*(sp7) + (1988432985638227/50000000000000 : ℝ)*(f.failure) + (8033097053664893/100000000000000 : ℝ)*(f.sum) + (44082765766121/6740000000000000000000000000 : ℝ)*base65 + (8613469705838960497/674000000000000000000000000000000 : ℝ)*base67 + (10723855874664960497/674000000000000000000000000000000 : ℝ)*base69 + (2354013912238960497/674000000000000000000000000000000 : ℝ)*base71 + (41156290219221/6740000000000000000000000000 : ℝ)*base73 + (26073430929684960497/674000000000000000000000000000000 : ℝ)*base75 + (5312901054218960497/674000000000000000000000000000000 : ℝ)*base77 + (5997103423222960497/674000000000000000000000000000000 : ℝ)*base79 + (66692543039261/6740000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (37208547/5000000000000000000000 : ℝ)*base90 + (37208547/5000000000000000000000 : ℝ)*base92 + (37208547/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1220_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1220_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1220_s7_0 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106506599/500000000 : ℝ)*x 0 + (5391610799/10000000000 : ℝ)*x 1 + (2633455307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106506599/500000000 : ℝ)^8413 ≤ (6475672096313/50000000000000 : ℝ)^6365 := by
    have hnat : (106506599 : ℕ)^8413*50000000000000^6365 ≤ 6475672096313^6365*500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106506599 500000000 6475672096313 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391610799/10000000000 : ℝ)^8413 ≤ (11049341590329/25000000000000 : ℝ)^6365 := by
    have hnat : (5391610799 : ℕ)^8413*25000000000000^6365 ≤ 11049341590329^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391610799 10000000000 11049341590329 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633455307/5000000000 : ℝ)^8413 ≤ (4285128942649/10000000000000 : ℝ)^6365 := by
    have hnat : (2633455307 : ℕ)^8413*10000000000000^6365 ≤ 4285128942649^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633455307 5000000000 4285128942649 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106506599/500000000 : ℝ), (5391610799/10000000000 : ℝ), (2633455307/5000000000 : ℝ)] ![(6475672096313/50000000000000 : ℝ), (11049341590329/25000000000000 : ℝ), (4285128942649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106506599/500000000 : ℝ)|^8413 ≤ (6475672096313/50000000000000 : ℝ)^6365
        have hw : |(-106506599/500000000 : ℝ)|=(106506599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391610799/10000000000 : ℝ)|^8413 ≤ (11049341590329/25000000000000 : ℝ)^6365
        have hw : |(5391610799/10000000000 : ℝ)|=(5391610799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633455307/5000000000 : ℝ)|^8413 ≤ (4285128942649/10000000000000 : ℝ)^6365
        have hw : |(2633455307/5000000000 : ℝ)|=(2633455307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_1 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336105679/2500000000 : ℝ)*x 0 + (-2193363317/10000000000 : ℝ)*x 1 + (2633455359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336105679/2500000000 : ℝ)^8413 ≤ (43686803147243/100000000000000 : ℝ)^6365 := by
    have hnat : (1336105679 : ℕ)^8413*100000000000000^6365 ≤ 43686803147243^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336105679 2500000000 43686803147243 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193363317/10000000000 : ℝ)^8413 ≤ (13461906292527/100000000000000 : ℝ)^6365 := by
    have hnat : (2193363317 : ℕ)^8413*100000000000000^6365 ≤ 13461906292527^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193363317 10000000000 13461906292527 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633455359/5000000000 : ℝ)^8413 ≤ (42851290544881/100000000000000 : ℝ)^6365 := by
    have hnat : (2633455359 : ℕ)^8413*100000000000000^6365 ≤ 42851290544881^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633455359 5000000000 42851290544881 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336105679/2500000000 : ℝ), (-2193363317/10000000000 : ℝ), (2633455359/5000000000 : ℝ)] ![(43686803147243/100000000000000 : ℝ), (13461906292527/100000000000000 : ℝ), (42851290544881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336105679/2500000000 : ℝ)|^8413 ≤ (43686803147243/100000000000000 : ℝ)^6365
        have hw : |(1336105679/2500000000 : ℝ)|=(1336105679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193363317/10000000000 : ℝ)|^8413 ≤ (13461906292527/100000000000000 : ℝ)^6365
        have hw : |(-2193363317/10000000000 : ℝ)|=(2193363317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633455359/5000000000 : ℝ)|^8413 ≤ (42851290544881/100000000000000 : ℝ)^6365
        have hw : |(2633455359/5000000000 : ℝ)|=(2633455359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_2 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344422791/10000000000 : ℝ)*x 0 + (658363823/1250000000 : ℝ)*x 1 + (-438672679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344422791/10000000000 : ℝ)^8413 ≤ (1747472158303/4000000000000 : ℝ)^6365 := by
    have hnat : (5344422791 : ℕ)^8413*4000000000000^6365 ≤ 1747472158303^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344422791 10000000000 1747472158303 4000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658363823/1250000000 : ℝ)^8413 ≤ (42851289103877/100000000000000 : ℝ)^6365 := by
    have hnat : (658363823 : ℕ)^8413*100000000000000^6365 ≤ 42851289103877^6365*1250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658363823 1250000000 42851289103877 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438672679/2000000000 : ℝ)^8413 ≤ (13461906925293/100000000000000 : ℝ)^6365 := by
    have hnat : (438672679 : ℕ)^8413*100000000000000^6365 ≤ 13461906925293^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438672679 2000000000 13461906925293 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344422791/10000000000 : ℝ), (658363823/1250000000 : ℝ), (-438672679/2000000000 : ℝ)] ![(1747472158303/4000000000000 : ℝ), (42851289103877/100000000000000 : ℝ), (13461906925293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344422791/10000000000 : ℝ)|^8413 ≤ (1747472158303/4000000000000 : ℝ)^6365
        have hw : |(5344422791/10000000000 : ℝ)|=(5344422791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658363823/1250000000 : ℝ)|^8413 ≤ (42851289103877/100000000000000 : ℝ)^6365
        have hw : |(658363823/1250000000 : ℝ)|=(658363823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438672679/2000000000 : ℝ)|^8413 ≤ (13461906925293/100000000000000 : ℝ)^6365
        have hw : |(-438672679/2000000000 : ℝ)|=(438672679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_3 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176899533/5000000000 : ℝ)*x 0 + (4229634869/10000000000 : ℝ)*x 1 + (112038087/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176899533/5000000000 : ℝ)^8413 ≤ (6663475484347/20000000000000 : ℝ)^6365 := by
    have hnat : (2176899533 : ℕ)^8413*20000000000000^6365 ≤ 6663475484347^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176899533 5000000000 6663475484347 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229634869/10000000000 : ℝ)^8413 ≤ (4008411002873/12500000000000 : ℝ)^6365 := by
    have hnat : (4229634869 : ℕ)^8413*12500000000000^6365 ≤ 4008411002873^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229634869 10000000000 4008411002873 12500000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112038087/250000000 : ℝ)^8413 ≤ (34615334535769/100000000000000 : ℝ)^6365 := by
    have hnat : (112038087 : ℕ)^8413*100000000000000^6365 ≤ 34615334535769^6365*250000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112038087 250000000 34615334535769 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176899533/5000000000 : ℝ), (4229634869/10000000000 : ℝ), (112038087/250000000 : ℝ)] ![(6663475484347/20000000000000 : ℝ), (4008411002873/12500000000000 : ℝ), (34615334535769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176899533/5000000000 : ℝ)|^8413 ≤ (6663475484347/20000000000000 : ℝ)^6365
        have hw : |(2176899533/5000000000 : ℝ)|=(2176899533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229634869/10000000000 : ℝ)|^8413 ≤ (4008411002873/12500000000000 : ℝ)^6365
        have hw : |(4229634869/10000000000 : ℝ)|=(4229634869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112038087/250000000 : ℝ)|^8413 ≤ (34615334535769/100000000000000 : ℝ)^6365
        have hw : |(112038087/250000000 : ℝ)|=(112038087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_4 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130136697/10000000000 : ℝ)*x 0 + (5267224821/10000000000 : ℝ)*x 1 + (1078259089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130136697/10000000000 : ℝ)^8413 ≤ (6475691050137/50000000000000 : ℝ)^6365 := by
    have hnat : (2130136697 : ℕ)^8413*50000000000000^6365 ≤ 6475691050137^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130136697 10000000000 6475691050137 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267224821/10000000000 : ℝ)^8413 ≤ (42854668366271/100000000000000 : ℝ)^6365 := by
    have hnat : (5267224821 : ℕ)^8413*100000000000000^6365 ≤ 42854668366271^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267224821 10000000000 42854668366271 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078259089/2000000000 : ℝ)^8413 ≤ (4419394952169/10000000000000 : ℝ)^6365 := by
    have hnat : (1078259089 : ℕ)^8413*10000000000000^6365 ≤ 4419394952169^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078259089 2000000000 4419394952169 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130136697/10000000000 : ℝ), (5267224821/10000000000 : ℝ), (1078259089/2000000000 : ℝ)] ![(6475691050137/50000000000000 : ℝ), (42854668366271/100000000000000 : ℝ), (4419394952169/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130136697/10000000000 : ℝ)|^8413 ≤ (6475691050137/50000000000000 : ℝ)^6365
        have hw : |(-2130136697/10000000000 : ℝ)|=(2130136697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267224821/10000000000 : ℝ)|^8413 ≤ (42854668366271/100000000000000 : ℝ)^6365
        have hw : |(5267224821/10000000000 : ℝ)|=(5267224821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078259089/2000000000 : ℝ)|^8413 ≤ (4419394952169/10000000000000 : ℝ)^6365
        have hw : |(1078259089/2000000000 : ℝ)|=(1078259089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_5 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656326349/5000000000 : ℝ)*x 0 + (-517244653/2500000000 : ℝ)*x 1 + (5391295329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656326349/5000000000 : ℝ)^8413 ≤ (866877497229/2000000000000 : ℝ)^6365 := by
    have hnat : (2656326349 : ℕ)^8413*2000000000000^6365 ≤ 866877497229^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656326349 5000000000 866877497229 2000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517244653/2500000000 : ℝ)^8413 ≤ (6231088426689/50000000000000 : ℝ)^6365 := by
    have hnat : (517244653 : ℕ)^8413*50000000000000^6365 ≤ 6231088426689^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517244653 2500000000 6231088426689 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391295329/10000000000 : ℝ)^8413 ≤ (883878965297/2000000000000 : ℝ)^6365 := by
    have hnat : (5391295329 : ℕ)^8413*2000000000000^6365 ≤ 883878965297^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391295329 10000000000 883878965297 2000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656326349/5000000000 : ℝ), (-517244653/2500000000 : ℝ), (5391295329/10000000000 : ℝ)] ![(866877497229/2000000000000 : ℝ), (6231088426689/50000000000000 : ℝ), (883878965297/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656326349/5000000000 : ℝ)|^8413 ≤ (866877497229/2000000000000 : ℝ)^6365
        have hw : |(2656326349/5000000000 : ℝ)|=(2656326349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517244653/2500000000 : ℝ)|^8413 ≤ (6231088426689/50000000000000 : ℝ)^6365
        have hw : |(-517244653/2500000000 : ℝ)|=(517244653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391295329/10000000000 : ℝ)|^8413 ≤ (883878965297/2000000000000 : ℝ)^6365
        have hw : |(5391295329/10000000000 : ℝ)|=(5391295329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_6 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062530527/2000000000 : ℝ)*x 0 + (2695647719/5000000000 : ℝ)*x 1 + (-41379571/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062530527/2000000000 : ℝ)^8413 ≤ (1733754967283/4000000000000 : ℝ)^6365 := by
    have hnat : (1062530527 : ℕ)^8413*4000000000000^6365 ≤ 1733754967283^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062530527 2000000000 1733754967283 4000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695647719/5000000000 : ℝ)^8413 ≤ (44193949445847/100000000000000 : ℝ)^6365 := by
    have hnat : (2695647719 : ℕ)^8413*100000000000000^6365 ≤ 44193949445847^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695647719 5000000000 44193949445847 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41379571/200000000 : ℝ)^8413 ≤ (1246217635977/10000000000000 : ℝ)^6365 := by
    have hnat : (41379571 : ℕ)^8413*10000000000000^6365 ≤ 1246217635977^6365*200000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41379571 200000000 1246217635977 10000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062530527/2000000000 : ℝ), (2695647719/5000000000 : ℝ), (-41379571/200000000 : ℝ)] ![(1733754967283/4000000000000 : ℝ), (44193949445847/100000000000000 : ℝ), (1246217635977/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062530527/2000000000 : ℝ)|^8413 ≤ (1733754967283/4000000000000 : ℝ)^6365
        have hw : |(1062530527/2000000000 : ℝ)|=(1062530527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695647719/5000000000 : ℝ)|^8413 ≤ (44193949445847/100000000000000 : ℝ)^6365
        have hw : |(2695647719/5000000000 : ℝ)|=(2695647719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41379571/200000000 : ℝ)|^8413 ≤ (1246217635977/10000000000000 : ℝ)^6365
        have hw : |(-41379571/200000000 : ℝ)|=(41379571/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s7_7 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176904287/5000000000 : ℝ)*x 0 + (4480888769/10000000000 : ℝ)*x 1 + (2115135939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176904287/5000000000 : ℝ)^8413 ≤ (16658736796379/50000000000000 : ℝ)^6365 := by
    have hnat : (2176904287 : ℕ)^8413*50000000000000^6365 ≤ 16658736796379^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176904287 5000000000 16658736796379 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480888769/10000000000 : ℝ)^8413 ≤ (1384354189511/4000000000000 : ℝ)^6365 := by
    have hnat : (4480888769 : ℕ)^8413*4000000000000^6365 ≤ 1384354189511^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480888769 10000000000 1384354189511 4000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115135939/5000000000 : ℝ)^8413 ≤ (2004604478513/6250000000000 : ℝ)^6365 := by
    have hnat : (2115135939 : ℕ)^8413*6250000000000^6365 ≤ 2004604478513^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115135939 5000000000 2004604478513 6250000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176904287/5000000000 : ℝ), (4480888769/10000000000 : ℝ), (2115135939/5000000000 : ℝ)] ![(16658736796379/50000000000000 : ℝ), (1384354189511/4000000000000 : ℝ), (2004604478513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176904287/5000000000 : ℝ)|^8413 ≤ (16658736796379/50000000000000 : ℝ)^6365
        have hw : |(2176904287/5000000000 : ℝ)|=(2176904287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480888769/10000000000 : ℝ)|^8413 ≤ (1384354189511/4000000000000 : ℝ)^6365
        have hw : |(4480888769/10000000000 : ℝ)|=(4480888769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115135939/5000000000 : ℝ)|^8413 ≤ (2004604478513/6250000000000 : ℝ)^6365
        have hw : |(2115135939/5000000000 : ℝ)|=(2115135939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1220_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11447/100000 : ℝ) ^ (2103/512 : ℝ) ≤ (2720693521985099/20000000000000000000 : ℝ) := by
    have hpowers : (11447/100000 : ℝ)^2103 ≤ (2720693521985099/20000000000000000000 : ℝ)^512 := by
      have hnat : (11447 : ℕ)^2103*20000000000000000000^512 ≤ 2720693521985099^512*100000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11447 100000 2720693521985099 20000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11447/100000 : ℝ)) (X := (2720693521985099/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (2103/512 : ℝ) ≤ (16002982608180567/50000000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^2103 ≤ (16002982608180567/50000000000000000000 : ℝ)^512 := by
      have hnat : (7049 : ℕ)^2103*50000000000000000000^512 ≤ 16002982608180567^512*50000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 16002982608180567 50000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (16002982608180567/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002720693521985099/10000000000000000000 : ℝ) ≤ (2500165579142343/2500000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (10002720693521985099/10000000000000000000 : ℝ)^512 ≤ (2500165579142343/2500000000000000 : ℝ)^2103 := by
      have hnat : (10002720693521985099 : ℕ)^512*2500000000000000^2103 ≤ 2500165579142343^2103*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002720693521985099 10000000000000000000 2500165579142343 2500000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500165579142343/2500000000000000 : ℝ)) (X := (10002720693521985099/10000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045609432826286629/100000000000000000000 : ℝ) ≤ (2000222044715557/2000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (100045609432826286629/100000000000000000000 : ℝ)^512 ≤ (2000222044715557/2000000000000000 : ℝ)^2103 := by
      have hnat : (100045609432826286629 : ℕ)^512*2000000000000000^2103 ≤ 2000222044715557^2103*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045609432826286629 100000000000000000000 2000222044715557 2000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222044715557/2000000000000000 : ℝ)) (X := (100045609432826286629/100000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016002982608180567/25000000000000000000 : ℝ) ≤ (5000779065293099/5000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (25016002982608180567/25000000000000000000 : ℝ)^512 ≤ (5000779065293099/5000000000000000 : ℝ)^2103 := by
      have hnat : (25016002982608180567 : ℕ)^512*5000000000000000^2103 ≤ 5000779065293099^2103*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016002982608180567 25000000000000000000 5000779065293099 5000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000779065293099/5000000000000000 : ℝ)) (X := (25016002982608180567/25000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2720693521985099/20000000000000000000 : ℝ) ≤ ((530030028363495959/530200000000000000 : ℝ)+2*(447907008413/265100000000000 : ℝ)*(11447/100000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (530030028363495959/530200000000000000 : ℝ)+2*(447907008413/265100000000000 : ℝ)*(11447/100000 : ℝ)=(2500165579142343/2500000000000000 : ℝ) by norm_num, show 1+2*(2720693521985099/20000000000000000000 : ℝ)=(10002720693521985099/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16002982608180567/50000000000000000000 : ℝ)+(2720693521985099/20000000000000000000 : ℝ) ≤ ((530030028363495959/530200000000000000 : ℝ)+(447907008413/265100000000000 : ℝ)*((7049/50000 : ℝ)+(11447/100000 : ℝ)))^(2103/512 : ℝ) := by
    rw [show (530030028363495959/530200000000000000 : ℝ)+(447907008413/265100000000000 : ℝ)*((7049/50000 : ℝ)+(11447/100000 : ℝ))=(2000222044715557/2000000000000000 : ℝ) by norm_num, show 1+(16002982608180567/50000000000000000000 : ℝ)+(2720693521985099/20000000000000000000 : ℝ)=(100045609432826286629/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16002982608180567/50000000000000000000 : ℝ) ≤ ((530030028363495959/530200000000000000 : ℝ)+2*(447907008413/265100000000000 : ℝ)*(7049/50000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (530030028363495959/530200000000000000 : ℝ)+2*(447907008413/265100000000000 : ℝ)*(7049/50000 : ℝ)=(5000779065293099/5000000000000000 : ℝ) by norm_num, show 1+2*(16002982608180567/50000000000000000000 : ℝ)=(25016002982608180567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (530030028363495959/530200000000000000 : ℝ)*(X 1 0+X 2 0)+(447907008413/265100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (530030028363495959/530200000000000000 : ℝ)) (alpha := (447907008413/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (530030028363495959/530200000000000000 : ℝ)*(X 0 1+X 2 1)+(447907008413/265100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (530030028363495959/530200000000000000 : ℝ)) (alpha := (447907008413/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (530030028363495959/530200000000000000 : ℝ)*(X 0 2+X 1 2)+(447907008413/265100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (530030028363495959/530200000000000000 : ℝ)) (alpha := (447907008413/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106506599/500000000 : ℝ)*X 0 0+(5391610799/10000000000 : ℝ)*X 0 1+(2633455307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336105679/2500000000 : ℝ)*X 1 0+(-2193363317/10000000000 : ℝ)*X 1 1+(2633455359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344422791/10000000000 : ℝ)*X 2 0+(658363823/1250000000 : ℝ)*X 2 1+(-438672679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176899533/5000000000 : ℝ)*X 0 0+(4229634869/10000000000 : ℝ)*X 0 1+(112038087/250000000 : ℝ)*X 0 2+(2176899533/5000000000 : ℝ)*X 1 0+(4229634869/10000000000 : ℝ)*X 1 1+(112038087/250000000 : ℝ)*X 1 2+(2176899533/5000000000 : ℝ)*X 2 0+(4229634869/10000000000 : ℝ)*X 2 1+(112038087/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130136697/10000000000 : ℝ)*X 0 0+(5267224821/10000000000 : ℝ)*X 0 1+(1078259089/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656326349/5000000000 : ℝ)*X 1 0+(-517244653/2500000000 : ℝ)*X 1 1+(5391295329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062530527/2000000000 : ℝ)*X 2 0+(2695647719/5000000000 : ℝ)*X 2 1+(-41379571/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176904287/5000000000 : ℝ)*X 0 0+(4480888769/10000000000 : ℝ)*X 0 1+(2115135939/5000000000 : ℝ)*X 0 2+(2176904287/5000000000 : ℝ)*X 1 0+(4480888769/10000000000 : ℝ)*X 1 1+(2115135939/5000000000 : ℝ)*X 1 2+(2176904287/5000000000 : ℝ)*X 2 0+(4480888769/10000000000 : ℝ)*X 2 1+(2115135939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148634196721468841014583559/13255000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77344149/4000000000000 : ℝ)*(base19) + (1883090209/100000000000000 : ℝ)*(base23) + (87141653/100000000000000 : ℝ)*(lower2) + (336245293/100000000000000 : ℝ)*(upper3) + (13651959/12500000000000 : ℝ)*(upper5) + (5994704026509467/100000000000000 : ℝ)*(major0) + (5994704026509467/100000000000000 : ℝ)*(major1) + (5994704026509467/100000000000000 : ℝ)*(major2) + (8019294946239957/100000000000000 : ℝ)*(sp0) + (1002418282815567/12500000000000 : ℝ)*(sp1) + (2004836578259513/25000000000000 : ℝ)*(sp2) + (1985015510088083/50000000000000 : ℝ)*(sp3) + (10649977661/20000000000000 : ℝ)*(sp4) + (28462933037/100000000000000 : ℝ)*(sp7) + (992514870777301/25000000000000 : ℝ)*(f.failure) + (8019348196128261/100000000000000 : ℝ)*(f.sum) + (28260741471969/3313750000000000000000000000 : ℝ)*base65 + (692087958748614147/53020000000000000000000000000000 : ℝ)*base68 + (834763598205294147/53020000000000000000000000000000 : ℝ)*base70 + (90276634412085853/53020000000000000000000000000000 : ℝ)*base71 + (57314920311573/6627500000000000000000000000 : ℝ)*base73 + (91258970080794147/53020000000000000000000000000000 : ℝ)*base76 + (1280464449123034147/53020000000000000000000000000000 : ℝ)*base78 + (219861528275014147/53020000000000000000000000000000 : ℝ)*base80 + (41318333328241/13255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (26252539/2500000000000000000000 : ℝ)*base89 + (26252539/2500000000000000000000 : ℝ)*base91 + (26252539/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140414870774381842501450413/26510000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (973114031/100000000000000 : ℝ)*(base19) + (945298261/100000000000000 : ℝ)*(base23) + (2248853/6250000000000 : ℝ)*(upper3) + (2320723/6250000000000 : ℝ)*(lower4) + (22521459/12500000000000 : ℝ)*(upper5) + (6025040616009769/100000000000000 : ℝ)*(major0) + (6025040616009769/100000000000000 : ℝ)*(major1) + (6025040616009769/100000000000000 : ℝ)*(major2) + (25646474167/100000000000000 : ℝ)*(sp1) + (25290191353/100000000000000 : ℝ)*(sp2) + (322397233128317/4000000000000 : ℝ)*(sp4) + (8059904208619727/100000000000000 : ℝ)*(sp5) + (8059904592718311/100000000000000 : ℝ)*(sp6) + (997537556813937/25000000000000 : ℝ)*(sp7) + (997537556813937/25000000000000 : ℝ)*(f.failure) + (322397233128317/4000000000000 : ℝ)*(f.sum) + (11130020103839/1656875000000000000000000000 : ℝ)*base65 + (794442581664522529/53020000000000000000000000000000 : ℝ)*base68 + (3662840575162529/53020000000000000000000000000000 : ℝ)*base70 + (584324823811817471/53020000000000000000000000000000 : ℝ)*base71 + (15586199802199/6627500000000000000000000000 : ℝ)*base74 + (599044327676442529/53020000000000000000000000000000 : ℝ)*base76 + (502320131748017471/53020000000000000000000000000000 : ℝ)*base77 + (1171172954528422529/53020000000000000000000000000000 : ℝ)*base80 + (1046033777243/207109375000000000000000000 : ℝ)*base81 + (12917857/2500000000000000000000 : ℝ)*base90 + (12917857/2500000000000000000000 : ℝ)*base92 + (12917857/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1220_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1220_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1220_s8_0 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130138073/10000000000 : ℝ)*x 0 + (5391566869/10000000000 : ℝ)*x 1 + (5266950323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130138073/10000000000 : ℝ)^8413 ≤ (12951393158351/100000000000000 : ℝ)^6365 := by
    have hnat : (2130138073 : ℕ)^8413*100000000000000^6365 ≤ 12951393158351^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130138073 10000000000 12951393158351 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391566869/10000000000 : ℝ)^8413 ≤ (2762305648677/6250000000000 : ℝ)^6365 := by
    have hnat : (5391566869 : ℕ)^8413*6250000000000^6365 ≤ 2762305648677^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391566869 10000000000 2762305648677 6250000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266950323/10000000000 : ℝ)^8413 ≤ (857034328963/2000000000000 : ℝ)^6365 := by
    have hnat : (5266950323 : ℕ)^8413*2000000000000^6365 ≤ 857034328963^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266950323 10000000000 857034328963 2000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130138073/10000000000 : ℝ), (5391566869/10000000000 : ℝ), (5266950323/10000000000 : ℝ)] ![(12951393158351/100000000000000 : ℝ), (2762305648677/6250000000000 : ℝ), (857034328963/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130138073/10000000000 : ℝ)|^8413 ≤ (12951393158351/100000000000000 : ℝ)^6365
        have hw : |(-2130138073/10000000000 : ℝ)|=(2130138073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391566869/10000000000 : ℝ)|^8413 ≤ (2762305648677/6250000000000 : ℝ)^6365
        have hw : |(5391566869/10000000000 : ℝ)|=(5391566869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266950323/10000000000 : ℝ)|^8413 ≤ (857034328963/2000000000000 : ℝ)^6365
        have hw : |(5266950323/10000000000 : ℝ)|=(5266950323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_1 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336102741/2500000000 : ℝ)*x 0 + (-1096663181/5000000000 : ℝ)*x 1 + (5266950403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336102741/2500000000 : ℝ)^8413 ≤ (21843338086801/50000000000000 : ℝ)^6365 := by
    have hnat : (1336102741 : ℕ)^8413*50000000000000^6365 ≤ 21843338086801^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336102741 2500000000 21843338086801 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096663181/5000000000 : ℝ)^8413 ≤ (13461606500211/100000000000000 : ℝ)^6365 := by
    have hnat : (1096663181 : ℕ)^8413*100000000000000^6365 ≤ 13461606500211^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096663181 5000000000 13461606500211 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266950403/10000000000 : ℝ)^8413 ≤ (42851717308453/100000000000000 : ℝ)^6365 := by
    have hnat : (5266950403 : ℕ)^8413*100000000000000^6365 ≤ 42851717308453^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266950403 10000000000 42851717308453 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336102741/2500000000 : ℝ), (-1096663181/5000000000 : ℝ), (5266950403/10000000000 : ℝ)] ![(21843338086801/50000000000000 : ℝ), (13461606500211/100000000000000 : ℝ), (42851717308453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336102741/2500000000 : ℝ)|^8413 ≤ (21843338086801/50000000000000 : ℝ)^6365
        have hw : |(1336102741/2500000000 : ℝ)|=(1336102741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096663181/5000000000 : ℝ)|^8413 ≤ (13461606500211/100000000000000 : ℝ)^6365
        have hw : |(-1096663181/5000000000 : ℝ)|=(1096663181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266950403/10000000000 : ℝ)|^8413 ≤ (42851717308453/100000000000000 : ℝ)^6365
        have hw : |(5266950403/10000000000 : ℝ)|=(5266950403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_2 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336102753/2500000000 : ℝ)*x 0 + (1053390061/2000000000 : ℝ)*x 1 + (-548331607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336102753/2500000000 : ℝ)^8413 ≤ (21843338346107/50000000000000 : ℝ)^6365 := by
    have hnat : (1336102753 : ℕ)^8413*50000000000000^6365 ≤ 21843338346107^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336102753 2500000000 21843338346107 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053390061/2000000000 : ℝ)^8413 ≤ (21425858127291/50000000000000 : ℝ)^6365 := by
    have hnat : (1053390061 : ℕ)^8413*50000000000000^6365 ≤ 21425858127291^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053390061 2000000000 21425858127291 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548331607/2500000000 : ℝ)^8413 ≤ (21538571257/160000000000 : ℝ)^6365 := by
    have hnat : (548331607 : ℕ)^8413*160000000000^6365 ≤ 21538571257^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548331607 2500000000 21538571257 160000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336102753/2500000000 : ℝ), (1053390061/2000000000 : ℝ), (-548331607/2500000000 : ℝ)] ![(21843338346107/50000000000000 : ℝ), (21425858127291/50000000000000 : ℝ), (21538571257/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336102753/2500000000 : ℝ)|^8413 ≤ (21843338346107/50000000000000 : ℝ)^6365
        have hw : |(1336102753/2500000000 : ℝ)|=(1336102753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053390061/2000000000 : ℝ)|^8413 ≤ (21425858127291/50000000000000 : ℝ)^6365
        have hw : |(1053390061/2000000000 : ℝ)|=(1053390061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548331607/2500000000 : ℝ)|^8413 ≤ (21538571257/160000000000 : ℝ)^6365
        have hw : |(-548331607/2500000000 : ℝ)|=(548331607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_3 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353801189/10000000000 : ℝ)*x 0 + (4229718937/10000000000 : ℝ)*x 1 + (2240719429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353801189/10000000000 : ℝ)^8413 ≤ (33317398895339/100000000000000 : ℝ)^6365 := by
    have hnat : (4353801189 : ℕ)^8413*100000000000000^6365 ≤ 33317398895339^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353801189 10000000000 33317398895339 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229718937/10000000000 : ℝ)^8413 ≤ (32068130472607/100000000000000 : ℝ)^6365 := by
    have hnat : (4229718937 : ℕ)^8413*100000000000000^6365 ≤ 32068130472607^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229718937 10000000000 32068130472607 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240719429/5000000000 : ℝ)^8413 ≤ (17307235304129/50000000000000 : ℝ)^6365 := by
    have hnat : (2240719429 : ℕ)^8413*50000000000000^6365 ≤ 17307235304129^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240719429 5000000000 17307235304129 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353801189/10000000000 : ℝ), (4229718937/10000000000 : ℝ), (2240719429/5000000000 : ℝ)] ![(33317398895339/100000000000000 : ℝ), (32068130472607/100000000000000 : ℝ), (17307235304129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353801189/10000000000 : ℝ)|^8413 ≤ (33317398895339/100000000000000 : ℝ)^6365
        have hw : |(4353801189/10000000000 : ℝ)|=(4353801189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229718937/10000000000 : ℝ)|^8413 ≤ (32068130472607/100000000000000 : ℝ)^6365
        have hw : |(4229718937/10000000000 : ℝ)|=(4229718937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240719429/5000000000 : ℝ)|^8413 ≤ (17307235304129/50000000000000 : ℝ)^6365
        have hw : |(2240719429/5000000000 : ℝ)|=(2240719429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_4 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130142937/10000000000 : ℝ)*x 0 + (1316816139/2500000000 : ℝ)*x 1 + (2695625689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130142937/10000000000 : ℝ)^8413 ≤ (2590286449477/20000000000000 : ℝ)^6365 := by
    have hnat : (2130142937 : ℕ)^8413*20000000000000^6365 ≤ 2590286449477^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130142937 10000000000 2590286449477 20000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316816139/2500000000 : ℝ)^8413 ≤ (10713773918933/25000000000000 : ℝ)^6365 := by
    have hnat : (1316816139 : ℕ)^8413*25000000000000^6365 ≤ 10713773918933^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316816139 2500000000 10713773918933 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695625689/5000000000 : ℝ)^8413 ≤ (11048368015949/25000000000000 : ℝ)^6365 := by
    have hnat : (2695625689 : ℕ)^8413*25000000000000^6365 ≤ 11048368015949^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695625689 5000000000 11048368015949 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130142937/10000000000 : ℝ), (1316816139/2500000000 : ℝ), (2695625689/5000000000 : ℝ)] ![(2590286449477/20000000000000 : ℝ), (10713773918933/25000000000000 : ℝ), (11048368015949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130142937/10000000000 : ℝ)|^8413 ≤ (2590286449477/20000000000000 : ℝ)^6365
        have hw : |(-2130142937/10000000000 : ℝ)|=(2130142937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316816139/2500000000 : ℝ)|^8413 ≤ (10713773918933/25000000000000 : ℝ)^6365
        have hw : |(1316816139/2500000000 : ℝ)|=(1316816139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695625689/5000000000 : ℝ)|^8413 ≤ (11048368015949/25000000000000 : ℝ)^6365
        have hw : |(2695625689/5000000000 : ℝ)|=(2695625689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_5 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312662067/10000000000 : ℝ)*x 0 + (-1034512279/5000000000 : ℝ)*x 1 + (5391252243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312662067/10000000000 : ℝ)^8413 ≤ (21671987947097/50000000000000 : ℝ)^6365 := by
    have hnat : (5312662067 : ℕ)^8413*50000000000000^6365 ≤ 21671987947097^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312662067 10000000000 21671987947097 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034512279/5000000000 : ℝ)^8413 ≤ (6231271324983/50000000000000 : ℝ)^6365 := by
    have hnat : (1034512279 : ℕ)^8413*50000000000000^6365 ≤ 6231271324983^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034512279 5000000000 6231271324983 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391252243/10000000000 : ℝ)^8413 ≤ (44193481435901/100000000000000 : ℝ)^6365 := by
    have hnat : (5391252243 : ℕ)^8413*100000000000000^6365 ≤ 44193481435901^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391252243 10000000000 44193481435901 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312662067/10000000000 : ℝ), (-1034512279/5000000000 : ℝ), (5391252243/10000000000 : ℝ)] ![(21671987947097/50000000000000 : ℝ), (6231271324983/50000000000000 : ℝ), (44193481435901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312662067/10000000000 : ℝ)|^8413 ≤ (21671987947097/50000000000000 : ℝ)^6365
        have hw : |(5312662067/10000000000 : ℝ)|=(5312662067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034512279/5000000000 : ℝ)|^8413 ≤ (6231271324983/50000000000000 : ℝ)^6365
        have hw : |(-1034512279/5000000000 : ℝ)|=(1034512279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391252243/10000000000 : ℝ)|^8413 ≤ (44193481435901/100000000000000 : ℝ)^6365
        have hw : |(5391252243/10000000000 : ℝ)|=(5391252243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_6 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312662557/10000000000 : ℝ)*x 0 + (1347812877/2500000000 : ℝ)*x 1 + (-1034512447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312662557/10000000000 : ℝ)^8413 ≤ (21671990589111/50000000000000 : ℝ)^6365 := by
    have hnat : (5312662557 : ℕ)^8413*50000000000000^6365 ≤ 21671990589111^6365*10000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312662557 10000000000 21671990589111 50000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347812877/2500000000 : ℝ)^8413 ≤ (138104604601/312500000000 : ℝ)^6365 := by
    have hnat : (1347812877 : ℕ)^8413*312500000000^6365 ≤ 138104604601^6365*2500000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347812877 2500000000 138104604601 312500000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034512447/5000000000 : ℝ)^8413 ≤ (12462545325021/100000000000000 : ℝ)^6365 := by
    have hnat : (1034512447 : ℕ)^8413*100000000000000^6365 ≤ 12462545325021^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034512447 5000000000 12462545325021 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312662557/10000000000 : ℝ), (1347812877/2500000000 : ℝ), (-1034512447/5000000000 : ℝ)] ![(21671990589111/50000000000000 : ℝ), (138104604601/312500000000 : ℝ), (12462545325021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312662557/10000000000 : ℝ)|^8413 ≤ (21671990589111/50000000000000 : ℝ)^6365
        have hw : |(5312662557/10000000000 : ℝ)|=(5312662557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347812877/2500000000 : ℝ)|^8413 ≤ (138104604601/312500000000 : ℝ)^6365
        have hw : |(1347812877/2500000000 : ℝ)|=(1347812877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034512447/5000000000 : ℝ)|^8413 ≤ (12462545325021/100000000000000 : ℝ)^6365
        have hw : |(-1034512447/5000000000 : ℝ)|=(1034512447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1220_s8_7 (p : ℝ) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272113157/625000000 : ℝ)*x 0 + (896161053/2000000000 : ℝ)*x 1 + (2115177493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272113157/625000000 : ℝ)^8413 ≤ (33317493195147/100000000000000 : ℝ)^6365 := by
    have hnat : (272113157 : ℕ)^8413*100000000000000^6365 ≤ 33317493195147^6365*625000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272113157 625000000 33317493195147 100000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896161053/2000000000 : ℝ)^8413 ≤ (8652000565757/25000000000000 : ℝ)^6365 := by
    have hnat : (896161053 : ℕ)^8413*25000000000000^6365 ≤ 8652000565757^6365*2000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896161053 2000000000 8652000565757 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115177493/5000000000 : ℝ)^8413 ≤ (8018626131487/25000000000000 : ℝ)^6365 := by
    have hnat : (2115177493 : ℕ)^8413*25000000000000^6365 ≤ 8018626131487^6365*5000000000^8413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115177493 5000000000 8018626131487 25000000000000 8413 6365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8413/2048 : ℝ)) 8413 6365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272113157/625000000 : ℝ), (896161053/2000000000 : ℝ), (2115177493/5000000000 : ℝ)] ![(33317493195147/100000000000000 : ℝ), (8652000565757/25000000000000 : ℝ), (8018626131487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272113157/625000000 : ℝ)|^8413 ≤ (33317493195147/100000000000000 : ℝ)^6365
        have hw : |(272113157/625000000 : ℝ)|=(272113157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896161053/2000000000 : ℝ)|^8413 ≤ (8652000565757/25000000000000 : ℝ)^6365
        have hw : |(896161053/2000000000 : ℝ)|=(896161053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115177493/5000000000 : ℝ)|^8413 ≤ (8018626131487/25000000000000 : ℝ)^6365
        have hw : |(2115177493/5000000000 : ℝ)|=(2115177493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1220_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2863/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11451/100000 : ℝ) ^ (2103/512 : ℝ) ≤ (13623003042379443/100000000000000000000 : ℝ) := by
    have hpowers : (11451/100000 : ℝ)^2103 ≤ (13623003042379443/100000000000000000000 : ℝ)^512 := by
      have hnat : (11451 : ℕ)^2103*100000000000000000000^512 ≤ 13623003042379443^512*100000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11451 100000 13623003042379443 100000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11451/100000 : ℝ)) (X := (13623003042379443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (2103/512 : ℝ) ≤ (31959366557348399/100000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^2103 ≤ (31959366557348399/100000000000000000000 : ℝ)^512 := by
      have hnat : (14093 : ℕ)^2103*100000000000000000000^512 ≤ 31959366557348399^512*100000^2103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 31959366557348399 100000000000000000000 2103 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (31959366557348399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013623003042379443/50000000000000000000 : ℝ) ≤ (10000663267599489/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (50013623003042379443/50000000000000000000 : ℝ)^512 ≤ (10000663267599489/10000000000000000 : ℝ)^2103 := by
      have hnat : (50013623003042379443 : ℕ)^512*10000000000000000^2103 ≤ 10000663267599489^2103*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013623003042379443 50000000000000000000 10000663267599489 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000663267599489/10000000000000000 : ℝ)) (X := (50013623003042379443/50000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022791184799863921/50000000000000000000 : ℝ) ≤ (2000221912983801/2000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (50022791184799863921/50000000000000000000 : ℝ)^512 ≤ (2000221912983801/2000000000000000 : ℝ)^2103 := by
      have hnat : (50022791184799863921 : ℕ)^512*2000000000000000^2103 ≤ 2000221912983801^2103*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022791184799863921 50000000000000000000 2000221912983801 2000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221912983801/2000000000000000 : ℝ)) (X := (50022791184799863921/50000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031959366557348399/50000000000000000000 : ℝ) ≤ (10001555862238521/10000000000000000 : ℝ) ^ (2103/512 : ℝ) := by
    have hpowers : (50031959366557348399/50000000000000000000 : ℝ)^512 ≤ (10001555862238521/10000000000000000 : ℝ)^2103 := by
      have hnat : (50031959366557348399 : ℕ)^512*10000000000000000^2103 ≤ 10001555862238521^2103*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031959366557348399 50000000000000000000 10001555862238521 10000000000000000 512 2103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001555862238521/10000000000000000 : ℝ)) (X := (50031959366557348399/50000000000000000000 : ℝ)) (by norm_num) 2103 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13623003042379443/100000000000000000000 : ℝ) ≤ ((13205765625893147253/13210000000000000000 : ℝ)+2*(111574329879/66050000000000 : ℝ)*(11451/100000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (13205765625893147253/13210000000000000000 : ℝ)+2*(111574329879/66050000000000 : ℝ)*(11451/100000 : ℝ)=(10000663267599489/10000000000000000 : ℝ) by norm_num, show 1+2*(13623003042379443/100000000000000000000 : ℝ)=(50013623003042379443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31959366557348399/100000000000000000000 : ℝ)+(13623003042379443/100000000000000000000 : ℝ) ≤ ((13205765625893147253/13210000000000000000 : ℝ)+(111574329879/66050000000000 : ℝ)*((14093/100000 : ℝ)+(11451/100000 : ℝ)))^(2103/512 : ℝ) := by
    rw [show (13205765625893147253/13210000000000000000 : ℝ)+(111574329879/66050000000000 : ℝ)*((14093/100000 : ℝ)+(11451/100000 : ℝ))=(2000221912983801/2000000000000000 : ℝ) by norm_num, show 1+(31959366557348399/100000000000000000000 : ℝ)+(13623003042379443/100000000000000000000 : ℝ)=(50022791184799863921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31959366557348399/100000000000000000000 : ℝ) ≤ ((13205765625893147253/13210000000000000000 : ℝ)+2*(111574329879/66050000000000 : ℝ)*(14093/100000 : ℝ))^(2103/512 : ℝ) := by
    rw [show (13205765625893147253/13210000000000000000 : ℝ)+2*(111574329879/66050000000000 : ℝ)*(14093/100000 : ℝ)=(10001555862238521/10000000000000000 : ℝ) by norm_num, show 1+2*(31959366557348399/100000000000000000000 : ℝ)=(50031959366557348399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13205765625893147253/13210000000000000000 : ℝ)*(X 1 0+X 2 0)+(111574329879/66050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13205765625893147253/13210000000000000000 : ℝ)) (alpha := (111574329879/66050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13205765625893147253/13210000000000000000 : ℝ)*(X 0 1+X 2 1)+(111574329879/66050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13205765625893147253/13210000000000000000 : ℝ)) (alpha := (111574329879/66050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13205765625893147253/13210000000000000000 : ℝ)*(X 0 2+X 1 2)+(111574329879/66050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2103/512 : ℝ)) (lo := (11451/100000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13205765625893147253/13210000000000000000 : ℝ)) (alpha := (111574329879/66050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130138073/10000000000 : ℝ)*X 0 0+(5391566869/10000000000 : ℝ)*X 0 1+(5266950323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336102741/2500000000 : ℝ)*X 1 0+(-1096663181/5000000000 : ℝ)*X 1 1+(5266950403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336102753/2500000000 : ℝ)*X 2 0+(1053390061/2000000000 : ℝ)*X 2 1+(-548331607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353801189/10000000000 : ℝ)*X 0 0+(4229718937/10000000000 : ℝ)*X 0 1+(2240719429/5000000000 : ℝ)*X 0 2+(4353801189/10000000000 : ℝ)*X 1 0+(4229718937/10000000000 : ℝ)*X 1 1+(2240719429/5000000000 : ℝ)*X 1 2+(4353801189/10000000000 : ℝ)*X 2 0+(4229718937/10000000000 : ℝ)*X 2 1+(2240719429/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130142937/10000000000 : ℝ)*X 0 0+(1316816139/2500000000 : ℝ)*X 0 1+(2695625689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312662067/10000000000 : ℝ)*X 1 0+(-1034512279/5000000000 : ℝ)*X 1 1+(5391252243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312662557/10000000000 : ℝ)*X 2 0+(1347812877/2500000000 : ℝ)*X 2 1+(-1034512447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272113157/625000000 : ℝ)*X 0 0+(896161053/2000000000 : ℝ)*X 0 1+(2115177493/5000000000 : ℝ)*X 0 2+(272113157/625000000 : ℝ)*X 1 0+(896161053/2000000000 : ℝ)*X 1 1+(2115177493/5000000000 : ℝ)*X 1 2+(272113157/625000000 : ℝ)*X 2 0+(896161053/2000000000 : ℝ)*X 2 1+(2115177493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1220_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12333841864664970695127/1321000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357503907/20000000000000 : ℝ)*(base19) + (1724058137/100000000000000 : ℝ)*(base23) + (72435043/100000000000000 : ℝ)*(lower2) + (287075857/100000000000000 : ℝ)*(upper3) + (46184597/50000000000000 : ℝ)*(upper5) + (299936108578211/5000000000000 : ℝ)*(major0) + (299936108578211/5000000000000 : ℝ)*(major1) + (299936108578211/5000000000000 : ℝ)*(major2) + (8024673354068749/100000000000000 : ℝ)*(sp0) + (250772553124269/3125000000000 : ℝ)*(sp1) + (4012360881719003/50000000000000 : ℝ)*(sp2) + (1986346153647143/50000000000000 : ℝ)*(sp3) + (25066713697/50000000000000 : ℝ)*(sp4) + (14118556561/50000000000000 : ℝ)*(sp7) + (248295034025463/6250000000000 : ℝ)*(f.failure) + (501545217968509/6250000000000 : ℝ)*(f.sum) + (9727190231071/1321000000000000000000000000 : ℝ)*base66 + (474563290040745617/66050000000000000000000000000000 : ℝ)*base68 + (564687800783154383/66050000000000000000000000000000 : ℝ)*base69 + (326664862872604383/66050000000000000000000000000000 : ℝ)*base71 + (1026647951823/165125000000000000000000000 : ℝ)*base74 + (41507853484904383/66050000000000000000000000000000 : ℝ)*base75 + (63491956085395617/66050000000000000000000000000000 : ℝ)*base78 + (1589353068844995617/66050000000000000000000000000000 : ℝ)*base80 + (27952117413/3302500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8974457/625000000000000000000 : ℝ)*base89 + (8974457/625000000000000000000 : ℝ)*base91 + (8974457/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18594414006042379755933/6605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (684992249/100000000000000 : ℝ)*(base19) + (1753742349/100000000000000 : ℝ)*(base23) + (163801903/20000000000000 : ℝ)*(lower1) + (5447529/3125000000000 : ℝ)*(upper2) + (187562451/100000000000000 : ℝ)*(upper3) + (3014526945468189/50000000000000 : ℝ)*(major0) + (3014526945468189/50000000000000 : ℝ)*(major1) + (3014526945468189/50000000000000 : ℝ)*(major2) + (272405413/50000000000000 : ℝ)*(sp1) + (6610165051/50000000000000 : ℝ)*(sp3) + (1613059924955057/20000000000000 : ℝ)*(sp4) + (8065298394972211/100000000000000 : ℝ)*(sp5) + (1008162233879117/12500000000000 : ℝ)*(sp6) + (1996397421463633/50000000000000 : ℝ)*(sp7) + (499101007907171/12500000000000 : ℝ)*(f.failure) + (1613059924955057/20000000000000 : ℝ)*(f.sum) + (1144173674399/6605000000000000000000000000 : ℝ)*base65 + (673720180971565183/660500000000000000000000000000000 : ℝ)*base68 + (5931974005849434817/660500000000000000000000000000000 : ℝ)*base69 + (3631463503834934817/660500000000000000000000000000000 : ℝ)*base71 + (3865852091277/3302500000000000000000000000 : ℝ)*base73 + (9813876656721065183/660500000000000000000000000000000 : ℝ)*base76 + (21252374345699434817/660500000000000000000000000000000 : ℝ)*base77 + (25496874923965565183/660500000000000000000000000000000 : ℝ)*base80 + (3186607297829/1651250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8603469/1250000000000000000000 : ℝ)*base89 + (8603469/1250000000000000000000 : ℝ)*base91 + (8603469/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1220_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1220_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1220_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1220_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1220_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1220_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2103/512 : ℝ) ≤ p) (hpb : p ≤ (8413/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150997839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1220_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
