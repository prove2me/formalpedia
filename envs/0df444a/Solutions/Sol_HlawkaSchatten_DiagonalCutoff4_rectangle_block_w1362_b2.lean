-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1362_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:39.60346+00:00
-- url     : https://prove2.me/submissions/19ed859e-b06e-44e9-b36e-83abfe44f6da

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
theorem support_rectangle_w1362_s6_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026815411/10000000000 : ℝ)*x 0 + (338230157/625000000 : ℝ)*x 1 + (5245196427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026815411/10000000000 : ℝ)^2161 ≤ (12347700916943/100000000000000 : ℝ)^1649 := by
    have hnat : (2026815411 : ℕ)^2161*100000000000000^1649 ≤ 12347700916943^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026815411 10000000000 12347700916943 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338230157/625000000 : ℝ)^2161 ≤ (2795209439529/6250000000000 : ℝ)^1649 := by
    have hnat : (338230157 : ℕ)^2161*6250000000000^1649 ≤ 2795209439529^1649*625000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338230157 625000000 2795209439529 6250000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245196427/10000000000 : ℝ)^2161 ≤ (21464474019129/50000000000000 : ℝ)^1649 := by
    have hnat : (5245196427 : ℕ)^2161*50000000000000^1649 ≤ 21464474019129^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245196427 10000000000 21464474019129 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026815411/10000000000 : ℝ), (338230157/625000000 : ℝ), (5245196427/10000000000 : ℝ)] ![(12347700916943/100000000000000 : ℝ), (2795209439529/6250000000000 : ℝ), (21464474019129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026815411/10000000000 : ℝ)|^2161 ≤ (12347700916943/100000000000000 : ℝ)^1649
        have hw : |(-2026815411/10000000000 : ℝ)|=(2026815411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338230157/625000000 : ℝ)|^2161 ≤ (2795209439529/6250000000000 : ℝ)^1649
        have hw : |(338230157/625000000 : ℝ)|=(338230157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245196427/10000000000 : ℝ)|^2161 ≤ (21464474019129/50000000000000 : ℝ)^1649
        have hw : |(5245196427/10000000000 : ℝ)|=(5245196427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348645947/10000000000 : ℝ)*x 0 + (-2111625823/10000000000 : ℝ)*x 1 + (5245196383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348645947/10000000000 : ℝ)^2161 ≤ (44041890828391/100000000000000 : ℝ)^1649 := by
    have hnat : (5348645947 : ℕ)^2161*100000000000000^1649 ≤ 44041890828391^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348645947 10000000000 44041890828391 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111625823/10000000000 : ℝ)^2161 ≤ (13029161596887/100000000000000 : ℝ)^1649 := by
    have hnat : (2111625823 : ℕ)^2161*100000000000000^1649 ≤ 13029161596887^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111625823 10000000000 13029161596887 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245196383/10000000000 : ℝ)^2161 ≤ (42928947566331/100000000000000 : ℝ)^1649 := by
    have hnat : (5245196383 : ℕ)^2161*100000000000000^1649 ≤ 42928947566331^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245196383 10000000000 42928947566331 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348645947/10000000000 : ℝ), (-2111625823/10000000000 : ℝ), (5245196383/10000000000 : ℝ)] ![(44041890828391/100000000000000 : ℝ), (13029161596887/100000000000000 : ℝ), (42928947566331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348645947/10000000000 : ℝ)|^2161 ≤ (44041890828391/100000000000000 : ℝ)^1649
        have hw : |(5348645947/10000000000 : ℝ)|=(5348645947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111625823/10000000000 : ℝ)|^2161 ≤ (13029161596887/100000000000000 : ℝ)^1649
        have hw : |(-2111625823/10000000000 : ℝ)|=(2111625823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245196383/10000000000 : ℝ)|^2161 ≤ (42928947566331/100000000000000 : ℝ)^1649
        have hw : |(5245196383/10000000000 : ℝ)|=(5245196383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348645961/10000000000 : ℝ)*x 0 + (5245196411/10000000000 : ℝ)*x 1 + (-2111625767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348645961/10000000000 : ℝ)^2161 ≤ (44041890979463/100000000000000 : ℝ)^1649 := by
    have hnat : (5348645961 : ℕ)^2161*100000000000000^1649 ≤ 44041890979463^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348645961 10000000000 44041890979463 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245196411/10000000000 : ℝ)^2161 ≤ (5366118483331/12500000000000 : ℝ)^1649 := by
    have hnat : (5245196411 : ℕ)^2161*12500000000000^1649 ≤ 5366118483331^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245196411 10000000000 5366118483331 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111625767/10000000000 : ℝ)^2161 ≤ (13029161144071/100000000000000 : ℝ)^1649 := by
    have hnat : (2111625767 : ℕ)^2161*100000000000000^1649 ≤ 13029161144071^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111625767 10000000000 13029161144071 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348645961/10000000000 : ℝ), (5245196411/10000000000 : ℝ), (-2111625767/10000000000 : ℝ)] ![(44041890979463/100000000000000 : ℝ), (5366118483331/12500000000000 : ℝ), (13029161144071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348645961/10000000000 : ℝ)|^2161 ≤ (44041890979463/100000000000000 : ℝ)^1649
        have hw : |(5348645961/10000000000 : ℝ)|=(5348645961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245196411/10000000000 : ℝ)|^2161 ≤ (5366118483331/12500000000000 : ℝ)^1649
        have hw : |(5245196411/10000000000 : ℝ)|=(5245196411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111625767/10000000000 : ℝ)|^2161 ≤ (13029161144071/100000000000000 : ℝ)^1649
        have hw : |(-2111625767/10000000000 : ℝ)|=(2111625767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (270088503/625000000 : ℝ)*x 0 + (4149051849/10000000000 : ℝ)*x 1 + (4500395083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270088503/625000000 : ℝ)^2161 ≤ (16651800024877/50000000000000 : ℝ)^1649 := by
    have hnat : (270088503 : ℕ)^2161*50000000000000^1649 ≤ 16651800024877^1649*625000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270088503 625000000 16651800024877 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149051849/10000000000 : ℝ)^2161 ≤ (31573690186851/100000000000000 : ℝ)^1649 := by
    have hnat : (4149051849 : ℕ)^2161*100000000000000^1649 ≤ 31573690186851^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149051849 10000000000 31573690186851 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500395083/10000000000 : ℝ)^2161 ≤ (35122709749459/100000000000000 : ℝ)^1649 := by
    have hnat : (4500395083 : ℕ)^2161*100000000000000^1649 ≤ 35122709749459^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500395083 10000000000 35122709749459 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270088503/625000000 : ℝ), (4149051849/10000000000 : ℝ), (4500395083/10000000000 : ℝ)] ![(16651800024877/50000000000000 : ℝ), (31573690186851/100000000000000 : ℝ), (35122709749459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270088503/625000000 : ℝ)|^2161 ≤ (16651800024877/50000000000000 : ℝ)^1649
        have hw : |(270088503/625000000 : ℝ)|=(270088503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149051849/10000000000 : ℝ)|^2161 ≤ (31573690186851/100000000000000 : ℝ)^1649
        have hw : |(4149051849/10000000000 : ℝ)|=(4149051849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500395083/10000000000 : ℝ)|^2161 ≤ (35122709749459/100000000000000 : ℝ)^1649
        have hw : |(4500395083/10000000000 : ℝ)|=(4500395083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013413929/5000000000 : ℝ)*x 0 + (524579391/1000000000 : ℝ)*x 1 + (5411081601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013413929/5000000000 : ℝ)^2161 ≤ (2469560058113/20000000000000 : ℝ)^1649 := by
    have hnat : (1013413929 : ℕ)^2161*20000000000000^1649 ≤ 2469560058113^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013413929 5000000000 2469560058113 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524579391/1000000000 : ℝ)^2161 ≤ (42935356530069/100000000000000 : ℝ)^1649 := by
    have hnat : (524579391 : ℕ)^2161*100000000000000^1649 ≤ 42935356530069^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524579391 1000000000 42935356530069 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411081601/10000000000 : ℝ)^2161 ≤ (22358421581707/50000000000000 : ℝ)^1649 := by
    have hnat : (5411081601 : ℕ)^2161*50000000000000^1649 ≤ 22358421581707^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411081601 10000000000 22358421581707 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013413929/5000000000 : ℝ), (524579391/1000000000 : ℝ), (5411081601/10000000000 : ℝ)] ![(2469560058113/20000000000000 : ℝ), (42935356530069/100000000000000 : ℝ), (22358421581707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013413929/5000000000 : ℝ)|^2161 ≤ (2469560058113/20000000000000 : ℝ)^1649
        have hw : |(-1013413929/5000000000 : ℝ)|=(1013413929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524579391/1000000000 : ℝ)|^2161 ≤ (42935356530069/100000000000000 : ℝ)^1649
        have hw : |(524579391/1000000000 : ℝ)|=(524579391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411081601/10000000000 : ℝ)|^2161 ≤ (22358421581707/50000000000000 : ℝ)^1649
        have hw : |(5411081601/10000000000 : ℝ)|=(5411081601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106113309/200000000 : ℝ)*x 0 + (-1945739547/10000000000 : ℝ)*x 1 + (5411082789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106113309/200000000 : ℝ)^2161 ≤ (21789336900199/50000000000000 : ℝ)^1649 := by
    have hnat : (106113309 : ℕ)^2161*50000000000000^1649 ≤ 21789336900199^1649*200000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106113309 200000000 21789336900199 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945739547/10000000000 : ℝ)^2161 ≤ (2926117537741/25000000000000 : ℝ)^1649 := by
    have hnat : (1945739547 : ℕ)^2161*25000000000000^1649 ≤ 2926117537741^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945739547 10000000000 2926117537741 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411082789/10000000000 : ℝ)^2161 ≤ (22358428014619/50000000000000 : ℝ)^1649 := by
    have hnat : (5411082789 : ℕ)^2161*50000000000000^1649 ≤ 22358428014619^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411082789 10000000000 22358428014619 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106113309/200000000 : ℝ), (-1945739547/10000000000 : ℝ), (5411082789/10000000000 : ℝ)] ![(21789336900199/50000000000000 : ℝ), (2926117537741/25000000000000 : ℝ), (22358428014619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106113309/200000000 : ℝ)|^2161 ≤ (21789336900199/50000000000000 : ℝ)^1649
        have hw : |(106113309/200000000 : ℝ)|=(106113309/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1945739547/10000000000 : ℝ)|^2161 ≤ (2926117537741/25000000000000 : ℝ)^1649
        have hw : |(-1945739547/10000000000 : ℝ)|=(1945739547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411082789/10000000000 : ℝ)|^2161 ≤ (22358428014619/50000000000000 : ℝ)^1649
        have hw : |(5411082789/10000000000 : ℝ)|=(5411082789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305665517/10000000000 : ℝ)*x 0 + (1352770723/2500000000 : ℝ)*x 1 + (-972869657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305665517/10000000000 : ℝ)^2161 ≤ (43578674521577/100000000000000 : ℝ)^1649 := by
    have hnat : (5305665517 : ℕ)^2161*100000000000000^1649 ≤ 43578674521577^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305665517 10000000000 43578674521577 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352770723/2500000000 : ℝ)^2161 ≤ (44716857144709/100000000000000 : ℝ)^1649 := by
    have hnat : (1352770723 : ℕ)^2161*100000000000000^1649 ≤ 44716857144709^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352770723 2500000000 44716857144709 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (972869657/5000000000 : ℝ)^2161 ≤ (1463058539273/12500000000000 : ℝ)^1649 := by
    have hnat : (972869657 : ℕ)^2161*12500000000000^1649 ≤ 1463058539273^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972869657 5000000000 1463058539273 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305665517/10000000000 : ℝ), (1352770723/2500000000 : ℝ), (-972869657/5000000000 : ℝ)] ![(43578674521577/100000000000000 : ℝ), (44716857144709/100000000000000 : ℝ), (1463058539273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305665517/10000000000 : ℝ)|^2161 ≤ (43578674521577/100000000000000 : ℝ)^1649
        have hw : |(5305665517/10000000000 : ℝ)|=(5305665517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352770723/2500000000 : ℝ)|^2161 ≤ (44716857144709/100000000000000 : ℝ)^1649
        have hw : |(1352770723/2500000000 : ℝ)|=(1352770723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-972869657/5000000000 : ℝ)|^2161 ≤ (1463058539273/12500000000000 : ℝ)^1649
        have hw : |(-972869657/5000000000 : ℝ)|=(972869657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s6_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1080360439/2500000000 : ℝ)*x 0 + (2249567281/5000000000 : ℝ)*x 1 + (2075159219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080360439/2500000000 : ℝ)^2161 ≤ (6660771937509/20000000000000 : ℝ)^1649 := by
    have hnat : (1080360439 : ℕ)^2161*20000000000000^1649 ≤ 6660771937509^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080360439 2500000000 6660771937509 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249567281/5000000000 : ℝ)^2161 ≤ (35109818272291/100000000000000 : ℝ)^1649 := by
    have hnat : (2249567281 : ℕ)^2161*100000000000000^1649 ≤ 35109818272291^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249567281 5000000000 35109818272291 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075159219/5000000000 : ℝ)^2161 ≤ (31586322034659/100000000000000 : ℝ)^1649 := by
    have hnat : (2075159219 : ℕ)^2161*100000000000000^1649 ≤ 31586322034659^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075159219 5000000000 31586322034659 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080360439/2500000000 : ℝ), (2249567281/5000000000 : ℝ), (2075159219/5000000000 : ℝ)] ![(6660771937509/20000000000000 : ℝ), (35109818272291/100000000000000 : ℝ), (31586322034659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080360439/2500000000 : ℝ)|^2161 ≤ (6660771937509/20000000000000 : ℝ)^1649
        have hw : |(1080360439/2500000000 : ℝ)|=(1080360439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249567281/5000000000 : ℝ)|^2161 ≤ (35109818272291/100000000000000 : ℝ)^1649
        have hw : |(2249567281/5000000000 : ℝ)|=(2249567281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2075159219/5000000000 : ℝ)|^2161 ≤ (31586322034659/100000000000000 : ℝ)^1649
        have hw : |(2075159219/5000000000 : ℝ)|=(2075159219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2239/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11189/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11189/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11189/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11189/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (2421582561309509/25000000000000000000 : ℝ) := by
    have hpowers : (11189/100000 : ℝ)^4321 ≤ (2421582561309509/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11189 : ℕ)^4321*25000000000000000000^1024 ≤ 2421582561309509^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11189 100000 2421582561309509 25000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11189/100000 : ℝ)) (X := (2421582561309509/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7363/50000 : ℝ) ^ (4321/1024 : ℝ) ≤ (7717654372077449/25000000000000000000 : ℝ) := by
    have hpowers : (7363/50000 : ℝ)^4321 ≤ (7717654372077449/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7363 : ℕ)^4321*25000000000000000000^1024 ≤ 7717654372077449^1024*50000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7363 50000 7717654372077449 25000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7363/50000 : ℝ)) (X := (7717654372077449/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502421582561309509/12500000000000000000 : ℝ) ≤ (10000459063604329/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (12502421582561309509/12500000000000000000 : ℝ)^1024 ≤ (10000459063604329/10000000000000000 : ℝ)^4321 := by
      have hnat : (12502421582561309509 : ℕ)^1024*10000000000000000^4321 ≤ 10000459063604329^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502421582561309509 12500000000000000000 10000459063604329 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000459063604329/10000000000000000 : ℝ)) (X := (12502421582561309509/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505069618466693479/12500000000000000000 : ℝ) ≤ (10000960978710773/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (12505069618466693479/12500000000000000000 : ℝ)^1024 ≤ (10000960978710773/10000000000000000 : ℝ)^4321 := by
      have hnat : (12505069618466693479 : ℕ)^1024*10000000000000000^4321 ≤ 10000960978710773^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505069618466693479 12500000000000000000 10000960978710773 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000960978710773/10000000000000000 : ℝ)) (X := (12505069618466693479/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507717654372077449/12500000000000000000 : ℝ) ≤ (10001462893817217/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (12507717654372077449/12500000000000000000 : ℝ)^1024 ≤ (10001462893817217/10000000000000000 : ℝ)^4321 := by
      have hnat : (12507717654372077449 : ℕ)^1024*10000000000000000^4321 ≤ 10001462893817217^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507717654372077449 12500000000000000000 10001462893817217 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001462893817217/10000000000000000 : ℝ)) (X := (12507717654372077449/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2421582561309509/25000000000000000000 : ℝ) ≤ ((35360391851716507841/35370000000000000000 : ℝ)+2*(125478776611/88425000000000 : ℝ)*(11189/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (35360391851716507841/35370000000000000000 : ℝ)+2*(125478776611/88425000000000 : ℝ)*(11189/100000 : ℝ)=(10000459063604329/10000000000000000 : ℝ) by norm_num, show 1+2*(2421582561309509/25000000000000000000 : ℝ)=(12502421582561309509/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7717654372077449/25000000000000000000 : ℝ)+(2421582561309509/25000000000000000000 : ℝ) ≤ ((35360391851716507841/35370000000000000000 : ℝ)+(125478776611/88425000000000 : ℝ)*((7363/50000 : ℝ)+(11189/100000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (35360391851716507841/35370000000000000000 : ℝ)+(125478776611/88425000000000 : ℝ)*((7363/50000 : ℝ)+(11189/100000 : ℝ))=(10000960978710773/10000000000000000 : ℝ) by norm_num, show 1+(7717654372077449/25000000000000000000 : ℝ)+(2421582561309509/25000000000000000000 : ℝ)=(12505069618466693479/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7717654372077449/25000000000000000000 : ℝ) ≤ ((35360391851716507841/35370000000000000000 : ℝ)+2*(125478776611/88425000000000 : ℝ)*(7363/50000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (35360391851716507841/35370000000000000000 : ℝ)+2*(125478776611/88425000000000 : ℝ)*(7363/50000 : ℝ)=(10001462893817217/10000000000000000 : ℝ) by norm_num, show 1+2*(7717654372077449/25000000000000000000 : ℝ)=(12507717654372077449/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35360391851716507841/35370000000000000000 : ℝ)*(X 1 0+X 2 0)+(125478776611/88425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (35360391851716507841/35370000000000000000 : ℝ)) (alpha := (125478776611/88425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35360391851716507841/35370000000000000000 : ℝ)*(X 0 1+X 2 1)+(125478776611/88425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (35360391851716507841/35370000000000000000 : ℝ)) (alpha := (125478776611/88425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35360391851716507841/35370000000000000000 : ℝ)*(X 0 2+X 1 2)+(125478776611/88425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (11189/100000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (35360391851716507841/35370000000000000000 : ℝ)) (alpha := (125478776611/88425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2026815411/10000000000 : ℝ)*X 0 0+(338230157/625000000 : ℝ)*X 0 1+(5245196427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348645947/10000000000 : ℝ)*X 1 0+(-2111625823/10000000000 : ℝ)*X 1 1+(5245196383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348645961/10000000000 : ℝ)*X 2 0+(5245196411/10000000000 : ℝ)*X 2 1+(-2111625767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270088503/625000000 : ℝ)*X 0 0+(4149051849/10000000000 : ℝ)*X 0 1+(4500395083/10000000000 : ℝ)*X 0 2+(270088503/625000000 : ℝ)*X 1 0+(4149051849/10000000000 : ℝ)*X 1 1+(4500395083/10000000000 : ℝ)*X 1 2+(270088503/625000000 : ℝ)*X 2 0+(4149051849/10000000000 : ℝ)*X 2 1+(4500395083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1013413929/5000000000 : ℝ)*X 0 0+(524579391/1000000000 : ℝ)*X 0 1+(5411081601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106113309/200000000 : ℝ)*X 1 0+(-1945739547/10000000000 : ℝ)*X 1 1+(5411082789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305665517/10000000000 : ℝ)*X 2 0+(1352770723/2500000000 : ℝ)*X 2 1+(-972869657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080360439/2500000000 : ℝ)*X 0 0+(2249567281/5000000000 : ℝ)*X 0 1+(2075159219/5000000000 : ℝ)*X 0 2+(1080360439/2500000000 : ℝ)*X 1 0+(2249567281/5000000000 : ℝ)*X 1 1+(2075159219/5000000000 : ℝ)*X 1 2+(1080360439/2500000000 : ℝ)*X 2 0+(2249567281/5000000000 : ℝ)*X 2 1+(2075159219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186289751429655090570533863/29475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29483953/2500000000000 : ℝ)*(base19) + (1094433703/100000000000000 : ℝ)*(base23) + (13458059/25000000000000 : ℝ)*(lower2) + (18205787/12500000000000 : ℝ)*(upper3) + (143495087/100000000000000 : ℝ)*(upper5) + (221319916670419/5000000000000 : ℝ)*(major0) + (221319916670419/5000000000000 : ℝ)*(major1) + (221319916670419/5000000000000 : ℝ)*(major2) + (1201305993545249/20000000000000 : ℝ)*(sp0) + (3003276109712491/50000000000000 : ℝ)*(sp1) + (6006552304349399/100000000000000 : ℝ)*(sp2) + (711557758212227/25000000000000 : ℝ)*(sp3) + (23431056857/100000000000000 : ℝ)*(sp4) + (12024509309/100000000000000 : ℝ)*(sp7) + (2846243057358217/100000000000000 : ℝ)*(f.failure) + (3003276699391551/50000000000000 : ℝ)*(f.sum) + (737067838691/141480000000000000000000000 : ℝ)*base66 + (624592161712951793/58950000000000000000000000000000 : ℝ)*base67 + (411356068976851793/58950000000000000000000000000000 : ℝ)*base69 + (841770252739051793/58950000000000000000000000000000 : ℝ)*base71 + (2056550203331/884250000000000000000000000 : ℝ)*base74 + (326437094642551793/58950000000000000000000000000000 : ℝ)*base75 + (190415227098301793/58950000000000000000000000000000 : ℝ)*base77 + (769577406585901793/58950000000000000000000000000000 : ℝ)*base79 + (18280302461743/3537000000000000000000000000 : ℝ)*base81 + (31779307/10000000000000000000000 : ℝ)*base90 + (31779307/10000000000000000000000 : ℝ)*base92 + (31779307/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330339671228645732904324679/49125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (344293009/20000000000000 : ℝ)*(base19) + (2229702469/100000000000000 : ℝ)*(base23) + (25936547/25000000000000 : ℝ)*(upper2) + (624121899/100000000000000 : ℝ)*(upper3) + (19832567/20000000000000 : ℝ)*(upper5) + (1114610644342281/25000000000000 : ℝ)*(major0) + (1114610644342281/25000000000000 : ℝ)*(major1) + (1114610644342281/25000000000000 : ℝ)*(major2) + (53324956917/100000000000000 : ℝ)*(sp1) + (82494649929/100000000000000 : ℝ)*(sp2) + (6050036925363261/100000000000000 : ℝ)*(sp4) + (6049981878941299/100000000000000 : ℝ)*(sp5) + (6049952201010863/100000000000000 : ℝ)*(sp6) + (1433424002612959/50000000000000 : ℝ)*(sp7) + (1433424002612959/50000000000000 : ℝ)*(f.failure) + (6050036925363261/100000000000000 : ℝ)*(f.sum) + (1954390749649/2947500000000000000000000000 : ℝ)*base66 + (377300843923358369/98250000000000000000000000000000 : ℝ)*base67 + (1322365774431608369/98250000000000000000000000000000 : ℝ)*base69 + (324697938252608369/98250000000000000000000000000000 : ℝ)*base71 + (239983503017/92109375000000000000000000 : ℝ)*base74 + (1577720151538358369/98250000000000000000000000000000 : ℝ)*base75 + (867803011886858369/98250000000000000000000000000000 : ℝ)*base77 + (2235589543607108369/98250000000000000000000000000000 : ℝ)*base79 + (11798561018047/5895000000000000000000000000 : ℝ)*base81 + (56829389/5000000000000000000000 : ℝ)*base90 + (56829389/5000000000000000000000 : ℝ)*base92 + (56829389/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1362_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1362_s7_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-202682003/1000000000 : ℝ)*x 0 + (5411634541/10000000000 : ℝ)*x 1 + (5245241427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202682003/1000000000 : ℝ)^2161 ≤ (617386889691/5000000000000 : ℝ)^1649 := by
    have hnat : (202682003 : ℕ)^2161*5000000000000^1649 ≤ 617386889691^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202682003 1000000000 617386889691 5000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411634541/10000000000 : ℝ)^2161 ≤ (2236141574903/5000000000000 : ℝ)^1649 := by
    have hnat : (5411634541 : ℕ)^2161*5000000000000^1649 ≤ 2236141574903^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411634541 10000000000 2236141574903 5000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245241427/10000000000 : ℝ)^2161 ≤ (21464715346009/50000000000000 : ℝ)^1649 := by
    have hnat : (5245241427 : ℕ)^2161*50000000000000^1649 ≤ 21464715346009^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245241427 10000000000 21464715346009 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202682003/1000000000 : ℝ), (5411634541/10000000000 : ℝ), (5245241427/10000000000 : ℝ)] ![(617386889691/5000000000000 : ℝ), (2236141574903/5000000000000 : ℝ), (21464715346009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202682003/1000000000 : ℝ)|^2161 ≤ (617386889691/5000000000000 : ℝ)^1649
        have hw : |(-202682003/1000000000 : ℝ)|=(202682003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411634541/10000000000 : ℝ)|^2161 ≤ (2236141574903/5000000000000 : ℝ)^1649
        have hw : |(5411634541/10000000000 : ℝ)|=(5411634541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245241427/10000000000 : ℝ)|^2161 ≤ (21464715346009/50000000000000 : ℝ)^1649
        have hw : |(5245241427/10000000000 : ℝ)|=(5245241427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337158479/2500000000 : ℝ)*x 0 + (-211158213/1000000000 : ℝ)*x 1 + (5245241427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337158479/2500000000 : ℝ)^2161 ≤ (1376305031361/3125000000000 : ℝ)^1649 := by
    have hnat : (1337158479 : ℕ)^2161*3125000000000^1649 ≤ 1376305031361^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337158479 2500000000 1376305031361 3125000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211158213/1000000000 : ℝ)^2161 ≤ (13028808296521/100000000000000 : ℝ)^1649 := by
    have hnat : (211158213 : ℕ)^2161*100000000000000^1649 ≤ 13028808296521^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211158213 1000000000 13028808296521 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245241427/10000000000 : ℝ)^2161 ≤ (21464715346009/50000000000000 : ℝ)^1649 := by
    have hnat : (5245241427 : ℕ)^2161*50000000000000^1649 ≤ 21464715346009^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245241427 10000000000 21464715346009 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337158479/2500000000 : ℝ), (-211158213/1000000000 : ℝ), (5245241427/10000000000 : ℝ)] ![(1376305031361/3125000000000 : ℝ), (13028808296521/100000000000000 : ℝ), (21464715346009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337158479/2500000000 : ℝ)|^2161 ≤ (1376305031361/3125000000000 : ℝ)^1649
        have hw : |(1337158479/2500000000 : ℝ)|=(1337158479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211158213/1000000000 : ℝ)|^2161 ≤ (13028808296521/100000000000000 : ℝ)^1649
        have hw : |(-211158213/1000000000 : ℝ)|=(211158213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245241427/10000000000 : ℝ)|^2161 ≤ (21464715346009/50000000000000 : ℝ)^1649
        have hw : |(5245241427/10000000000 : ℝ)|=(5245241427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337158479/2500000000 : ℝ)*x 0 + (5245241427/10000000000 : ℝ)*x 1 + (-211158213/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337158479/2500000000 : ℝ)^2161 ≤ (1376305031361/3125000000000 : ℝ)^1649 := by
    have hnat : (1337158479 : ℕ)^2161*3125000000000^1649 ≤ 1376305031361^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337158479 2500000000 1376305031361 3125000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245241427/10000000000 : ℝ)^2161 ≤ (21464715346009/50000000000000 : ℝ)^1649 := by
    have hnat : (5245241427 : ℕ)^2161*50000000000000^1649 ≤ 21464715346009^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245241427 10000000000 21464715346009 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211158213/1000000000 : ℝ)^2161 ≤ (13028808296521/100000000000000 : ℝ)^1649 := by
    have hnat : (211158213 : ℕ)^2161*100000000000000^1649 ≤ 13028808296521^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211158213 1000000000 13028808296521 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337158479/2500000000 : ℝ), (5245241427/10000000000 : ℝ), (-211158213/1000000000 : ℝ)] ![(1376305031361/3125000000000 : ℝ), (21464715346009/50000000000000 : ℝ), (13028808296521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337158479/2500000000 : ℝ)|^2161 ≤ (1376305031361/3125000000000 : ℝ)^1649
        have hw : |(1337158479/2500000000 : ℝ)|=(1337158479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245241427/10000000000 : ℝ)|^2161 ≤ (21464715346009/50000000000000 : ℝ)^1649
        have hw : |(5245241427/10000000000 : ℝ)|=(5245241427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211158213/1000000000 : ℝ)|^2161 ≤ (13028808296521/100000000000000 : ℝ)^1649
        have hw : |(-211158213/1000000000 : ℝ)|=(211158213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4321419263/10000000000 : ℝ)*x 0 + (2074574847/5000000000 : ℝ)*x 1 + (4500296501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321419263/10000000000 : ℝ)^2161 ≤ (33303632519601/100000000000000 : ℝ)^1649 := by
    have hnat : (4321419263 : ℕ)^2161*100000000000000^1649 ≤ 33303632519601^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321419263 10000000000 33303632519601 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074574847/5000000000 : ℝ)^2161 ≤ (7893666491099/25000000000000 : ℝ)^1649 := by
    have hnat : (2074574847 : ℕ)^2161*25000000000000^1649 ≤ 7893666491099^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074574847 5000000000 7893666491099 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500296501/10000000000 : ℝ)^2161 ≤ (2195106343803/6250000000000 : ℝ)^1649 := by
    have hnat : (4500296501 : ℕ)^2161*6250000000000^1649 ≤ 2195106343803^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500296501 10000000000 2195106343803 6250000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321419263/10000000000 : ℝ), (2074574847/5000000000 : ℝ), (4500296501/10000000000 : ℝ)] ![(33303632519601/100000000000000 : ℝ), (7893666491099/25000000000000 : ℝ), (2195106343803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321419263/10000000000 : ℝ)|^2161 ≤ (33303632519601/100000000000000 : ℝ)^1649
        have hw : |(4321419263/10000000000 : ℝ)|=(4321419263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2074574847/5000000000 : ℝ)|^2161 ≤ (7893666491099/25000000000000 : ℝ)^1649
        have hw : |(2074574847/5000000000 : ℝ)|=(2074574847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500296501/10000000000 : ℝ)|^2161 ≤ (2195106343803/6250000000000 : ℝ)^1649
        have hw : |(4500296501/10000000000 : ℝ)|=(4500296501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026831983/10000000000 : ℝ)*x 0 + (5245837817/10000000000 : ℝ)*x 1 + (5411035073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026831983/10000000000 : ℝ)^2161 ≤ (12347833223537/100000000000000 : ℝ)^1649 := by
    have hnat : (2026831983 : ℕ)^2161*100000000000000^1649 ≤ 12347833223537^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026831983 10000000000 12347833223537 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245837817/10000000000 : ℝ)^2161 ≤ (8587165495469/20000000000000 : ℝ)^1649 := by
    have hnat : (5245837817 : ℕ)^2161*20000000000000^1649 ≤ 8587165495469^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245837817 10000000000 8587165495469 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411035073/10000000000 : ℝ)^2161 ≤ (44716339274307/100000000000000 : ℝ)^1649 := by
    have hnat : (5411035073 : ℕ)^2161*100000000000000^1649 ≤ 44716339274307^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411035073 10000000000 44716339274307 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026831983/10000000000 : ℝ), (5245837817/10000000000 : ℝ), (5411035073/10000000000 : ℝ)] ![(12347833223537/100000000000000 : ℝ), (8587165495469/20000000000000 : ℝ), (44716339274307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026831983/10000000000 : ℝ)|^2161 ≤ (12347833223537/100000000000000 : ℝ)^1649
        have hw : |(-2026831983/10000000000 : ℝ)|=(2026831983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245837817/10000000000 : ℝ)|^2161 ≤ (8587165495469/20000000000000 : ℝ)^1649
        have hw : |(5245837817/10000000000 : ℝ)|=(5245837817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411035073/10000000000 : ℝ)|^2161 ≤ (44716339274307/100000000000000 : ℝ)^1649
        have hw : |(5411035073/10000000000 : ℝ)|=(5411035073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305677613/10000000000 : ℝ)*x 0 + (-1945788491/10000000000 : ℝ)*x 1 + (2705517537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305677613/10000000000 : ℝ)^2161 ≤ (43578804721339/100000000000000 : ℝ)^1649 := by
    have hnat : (5305677613 : ℕ)^2161*100000000000000^1649 ≤ 43578804721339^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305677613 10000000000 43578804721339 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945788491/10000000000 : ℝ)^2161 ≤ (1463106998323/12500000000000 : ℝ)^1649 := by
    have hnat : (1945788491 : ℕ)^2161*12500000000000^1649 ≤ 1463106998323^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945788491 10000000000 1463106998323 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705517537/5000000000 : ℝ)^2161 ≤ (44716339285137/100000000000000 : ℝ)^1649 := by
    have hnat : (2705517537 : ℕ)^2161*100000000000000^1649 ≤ 44716339285137^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705517537 5000000000 44716339285137 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305677613/10000000000 : ℝ), (-1945788491/10000000000 : ℝ), (2705517537/5000000000 : ℝ)] ![(43578804721339/100000000000000 : ℝ), (1463106998323/12500000000000 : ℝ), (44716339285137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305677613/10000000000 : ℝ)|^2161 ≤ (43578804721339/100000000000000 : ℝ)^1649
        have hw : |(5305677613/10000000000 : ℝ)|=(5305677613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1945788491/10000000000 : ℝ)|^2161 ≤ (1463106998323/12500000000000 : ℝ)^1649
        have hw : |(-1945788491/10000000000 : ℝ)|=(1945788491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705517537/5000000000 : ℝ)|^2161 ≤ (44716339285137/100000000000000 : ℝ)^1649
        have hw : |(2705517537/5000000000 : ℝ)|=(2705517537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305677613/10000000000 : ℝ)*x 0 + (5411035073/10000000000 : ℝ)*x 1 + (-1945788491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305677613/10000000000 : ℝ)^2161 ≤ (43578804721339/100000000000000 : ℝ)^1649 := by
    have hnat : (5305677613 : ℕ)^2161*100000000000000^1649 ≤ 43578804721339^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305677613 10000000000 43578804721339 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411035073/10000000000 : ℝ)^2161 ≤ (44716339274307/100000000000000 : ℝ)^1649 := by
    have hnat : (5411035073 : ℕ)^2161*100000000000000^1649 ≤ 44716339274307^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411035073 10000000000 44716339274307 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945788491/10000000000 : ℝ)^2161 ≤ (1463106998323/12500000000000 : ℝ)^1649 := by
    have hnat : (1945788491 : ℕ)^2161*12500000000000^1649 ≤ 1463106998323^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945788491 10000000000 1463106998323 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305677613/10000000000 : ℝ), (5411035073/10000000000 : ℝ), (-1945788491/10000000000 : ℝ)] ![(43578804721339/100000000000000 : ℝ), (44716339274307/100000000000000 : ℝ), (1463106998323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305677613/10000000000 : ℝ)|^2161 ≤ (43578804721339/100000000000000 : ℝ)^1649
        have hw : |(5305677613/10000000000 : ℝ)|=(5305677613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411035073/10000000000 : ℝ)|^2161 ≤ (44716339274307/100000000000000 : ℝ)^1649
        have hw : |(5411035073/10000000000 : ℝ)|=(5411035073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945788491/10000000000 : ℝ)|^2161 ≤ (1463106998323/12500000000000 : ℝ)^1649
        have hw : |(-1945788491/10000000000 : ℝ)|=(1945788491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_s7_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864288897/2000000000 : ℝ)*x 0 + (2249518953/5000000000 : ℝ)*x 1 + (2075207391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864288897/2000000000 : ℝ)^2161 ≤ (8325971812273/25000000000000 : ℝ)^1649 := by
    have hnat : (864288897 : ℕ)^2161*25000000000000^1649 ≤ 8325971812273^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864288897 2000000000 8325971812273 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249518953/5000000000 : ℝ)^2161 ≤ (35108829807783/100000000000000 : ℝ)^1649 := by
    have hnat : (2249518953 : ℕ)^2161*100000000000000^1649 ≤ 35108829807783^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249518953 5000000000 35108829807783 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075207391/5000000000 : ℝ)^2161 ≤ (15793641467103/50000000000000 : ℝ)^1649 := by
    have hnat : (2075207391 : ℕ)^2161*50000000000000^1649 ≤ 15793641467103^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075207391 5000000000 15793641467103 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864288897/2000000000 : ℝ), (2249518953/5000000000 : ℝ), (2075207391/5000000000 : ℝ)] ![(8325971812273/25000000000000 : ℝ), (35108829807783/100000000000000 : ℝ), (15793641467103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864288897/2000000000 : ℝ)|^2161 ≤ (8325971812273/25000000000000 : ℝ)^1649
        have hw : |(864288897/2000000000 : ℝ)|=(864288897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249518953/5000000000 : ℝ)|^2161 ≤ (35108829807783/100000000000000 : ℝ)^1649
        have hw : |(2249518953/5000000000 : ℝ)|=(2249518953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2075207391/5000000000 : ℝ)|^2161 ≤ (15793641467103/50000000000000 : ℝ)^1649
        have hw : |(2075207391/5000000000 : ℝ)|=(2075207391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2799/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2239/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2239/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2239/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2239/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2239/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2239/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2239/20000 : ℝ) ^ (4321/1024 : ℝ) ≤ (1213533413389731/12500000000000000000 : ℝ) := by
    have hpowers : (2239/20000 : ℝ)^4321 ≤ (1213533413389731/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2239 : ℕ)^4321*12500000000000000000^1024 ≤ 1213533413389731^1024*20000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2239 20000 1213533413389731 12500000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2239/20000 : ℝ)) (X := (1213533413389731/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (4321/1024 : ℝ) ≤ (7704394137219103/25000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^4321 ≤ (7704394137219103/25000000000000000000 : ℝ)^1024 := by
      have hnat : (92 : ℕ)^4321*25000000000000000000^1024 ≤ 7704394137219103^1024*625^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 7704394137219103 25000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (7704394137219103/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251213533413389731/6250000000000000000 : ℝ) ≤ (125005751289863/125000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (6251213533413389731/6250000000000000000 : ℝ)^1024 ≤ (125005751289863/125000000000000 : ℝ)^4321 := by
      have hnat : (6251213533413389731 : ℕ)^1024*125000000000000^4321 ≤ 125005751289863^4321*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251213533413389731 6250000000000000000 125005751289863 125000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125005751289863/125000000000000 : ℝ)) (X := (6251213533413389731/6250000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002026292192799713/5000000000000000000 : ℝ) ≤ (2000192048366447/2000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (5002026292192799713/5000000000000000000 : ℝ)^1024 ≤ (2000192048366447/2000000000000000 : ℝ)^4321 := by
      have hnat : (5002026292192799713 : ℕ)^1024*2000000000000000^4321 ≤ 2000192048366447^4321*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002026292192799713 5000000000000000000 2000192048366447 2000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000192048366447/2000000000000000 : ℝ)) (X := (5002026292192799713/5000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507704394137219103/12500000000000000000 : ℝ) ≤ (1000146038047543/1000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (12507704394137219103/12500000000000000000 : ℝ)^1024 ≤ (1000146038047543/1000000000000000 : ℝ)^4321 := by
      have hnat : (12507704394137219103 : ℕ)^1024*1000000000000000^4321 ≤ 1000146038047543^4321*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507704394137219103 12500000000000000000 1000146038047543 1000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000146038047543/1000000000000000 : ℝ)) (X := (12507704394137219103/12500000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1213533413389731/12500000000000000000 : ℝ) ≤ ((234936158396801533/235000000000000000 : ℝ)+2*(33342576213/23500000000000 : ℝ)*(2239/20000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (234936158396801533/235000000000000000 : ℝ)+2*(33342576213/23500000000000 : ℝ)*(2239/20000 : ℝ)=(125005751289863/125000000000000 : ℝ) by norm_num, show 1+2*(1213533413389731/12500000000000000000 : ℝ)=(6251213533413389731/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7704394137219103/25000000000000000000 : ℝ)+(1213533413389731/12500000000000000000 : ℝ) ≤ ((234936158396801533/235000000000000000 : ℝ)+(33342576213/23500000000000 : ℝ)*((92/625 : ℝ)+(2239/20000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (234936158396801533/235000000000000000 : ℝ)+(33342576213/23500000000000 : ℝ)*((92/625 : ℝ)+(2239/20000 : ℝ))=(2000192048366447/2000000000000000 : ℝ) by norm_num, show 1+(7704394137219103/25000000000000000000 : ℝ)+(1213533413389731/12500000000000000000 : ℝ)=(5002026292192799713/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7704394137219103/25000000000000000000 : ℝ) ≤ ((234936158396801533/235000000000000000 : ℝ)+2*(33342576213/23500000000000 : ℝ)*(92/625 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (234936158396801533/235000000000000000 : ℝ)+2*(33342576213/23500000000000 : ℝ)*(92/625 : ℝ)=(1000146038047543/1000000000000000 : ℝ) by norm_num, show 1+2*(7704394137219103/25000000000000000000 : ℝ)=(12507704394137219103/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (234936158396801533/235000000000000000 : ℝ)*(X 1 0+X 2 0)+(33342576213/23500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (2239/20000 : ℝ)) (hi := (92/625 : ℝ)) (c := (234936158396801533/235000000000000000 : ℝ)) (alpha := (33342576213/23500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (234936158396801533/235000000000000000 : ℝ)*(X 0 1+X 2 1)+(33342576213/23500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (2239/20000 : ℝ)) (hi := (92/625 : ℝ)) (c := (234936158396801533/235000000000000000 : ℝ)) (alpha := (33342576213/23500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (234936158396801533/235000000000000000 : ℝ)*(X 0 2+X 1 2)+(33342576213/23500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (2239/20000 : ℝ)) (hi := (92/625 : ℝ)) (c := (234936158396801533/235000000000000000 : ℝ)) (alpha := (33342576213/23500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-202682003/1000000000 : ℝ)*X 0 0+(5411634541/10000000000 : ℝ)*X 0 1+(5245241427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337158479/2500000000 : ℝ)*X 1 0+(-211158213/1000000000 : ℝ)*X 1 1+(5245241427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337158479/2500000000 : ℝ)*X 2 0+(5245241427/10000000000 : ℝ)*X 2 1+(-211158213/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321419263/10000000000 : ℝ)*X 0 0+(2074574847/5000000000 : ℝ)*X 0 1+(4500296501/10000000000 : ℝ)*X 0 2+(4321419263/10000000000 : ℝ)*X 1 0+(2074574847/5000000000 : ℝ)*X 1 1+(4500296501/10000000000 : ℝ)*X 1 2+(4321419263/10000000000 : ℝ)*X 2 0+(2074574847/5000000000 : ℝ)*X 2 1+(4500296501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2026831983/10000000000 : ℝ)*X 0 0+(5245837817/10000000000 : ℝ)*X 0 1+(5411035073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305677613/10000000000 : ℝ)*X 1 0+(-1945788491/10000000000 : ℝ)*X 1 1+(2705517537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305677613/10000000000 : ℝ)*X 2 0+(5411035073/10000000000 : ℝ)*X 2 1+(-1945788491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864288897/2000000000 : ℝ)*X 0 0+(2249518953/5000000000 : ℝ)*X 0 1+(2075207391/5000000000 : ℝ)*X 0 2+(864288897/2000000000 : ℝ)*X 1 0+(2249518953/5000000000 : ℝ)*X 1 1+(2075207391/5000000000 : ℝ)*X 1 2+(864288897/2000000000 : ℝ)*X 2 0+(2249518953/5000000000 : ℝ)*X 2 1+(2075207391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34831586258311321564082709/5875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (553374767/50000000000000 : ℝ)*(base19) + (32215641/3125000000000 : ℝ)*(base23) + (20284433/50000000000000 : ℝ)*(lower2) + (7446273/5000000000000 : ℝ)*(upper3) + (46590521/50000000000000 : ℝ)*(upper5) + (2214436177479109/50000000000000 : ℝ)*(major0) + (2214436177479109/50000000000000 : ℝ)*(major1) + (2214436177479109/50000000000000 : ℝ)*(major2) + (6009887862908779/100000000000000 : ℝ)*(sp0) + (6009909513800029/100000000000000 : ℝ)*(sp1) + (6009909589649051/100000000000000 : ℝ)*(sp2) + (177988888062217/6250000000000 : ℝ)*(sp3) + (22757640783/100000000000000 : ℝ)*(sp4) + (1168274537/10000000000000 : ℝ)*(sp7) + (1423916945870421/50000000000000 : ℝ)*(f.failure) + (6009910620549563/100000000000000 : ℝ)*(f.sum) + (3963092075791/1175000000000000000000000000 : ℝ)*base66 + (55283439347344097/11750000000000000000000000000000 : ℝ)*base67 + (169929767771844097/11750000000000000000000000000000 : ℝ)*base69 + (78748084643655903/11750000000000000000000000000000 : ℝ)*base72 + (958098580571/293750000000000000000000000 : ℝ)*base73 + (164952096577594097/11750000000000000000000000000000 : ℝ)*base75 + (20367511070344097/11750000000000000000000000000000 : ℝ)*base77 + (19505423769905903/11750000000000000000000000000000 : ℝ)*base80 + (559662344323/146875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (33016591/5000000000000000000000 : ℝ)*base90 + (33016591/5000000000000000000000 : ℝ)*base92 + (33016591/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101294076293957086463532219/11750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1474669529/100000000000000 : ℝ)*(base19) + (320299927/20000000000000 : ℝ)*(base23) + (502883969/100000000000000 : ℝ)*(lower1) + (34888407/20000000000000 : ℝ)*(upper3) + (57912093/100000000000000 : ℝ)*(lower4) + (89206699/50000000000000 : ℝ)*(upper5) + (4460875143519619/100000000000000 : ℝ)*(major0) + (4460875143519619/100000000000000 : ℝ)*(major1) + (4460875143519619/100000000000000 : ℝ)*(major2) + (2183587343/100000000000000 : ℝ)*(sp2) + (3026668908269461/50000000000000 : ℝ)*(sp4) + (3026668170934697/50000000000000 : ℝ)*(sp5) + (756666753931493/12500000000000 : ℝ)*(sp6) + (2868412183141213/100000000000000 : ℝ)*(sp7) + (2868412183141213/100000000000000 : ℝ)*(f.failure) + (3026668908269461/50000000000000 : ℝ)*(f.sum) + (1769877298761/587500000000000000000000000 : ℝ)*base65 + (639600582641245927/23500000000000000000000000000000 : ℝ)*base67 + (92053200071245927/23500000000000000000000000000000 : ℝ)*base69 + (2625153098628745927/23500000000000000000000000000000 : ℝ)*base71 + (1487784482147/1175000000000000000000000000 : ℝ)*base73 + (1065310375403754073/23500000000000000000000000000000 : ℝ)*base76 + (36191507685745927/23500000000000000000000000000000 : ℝ)*base77 + (65269629185254073/23500000000000000000000000000000 : ℝ)*base80 + (273565393247/1175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (61458777/10000000000000000000000 : ℝ)*base89 + (61458777/10000000000000000000000 : ℝ)*base91 + (61458777/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1362_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2239/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1362_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1362_box_0 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1861134969/10000000000 : ℝ)*x 0 + (538910253/1000000000 : ℝ)*x 1 + (5389103119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1861134969/10000000000 : ℝ)^2161 ≤ (11042065489383/100000000000000 : ℝ)^1649 := by
    have hnat : (1861134969 : ℕ)^2161*100000000000000^1649 ≤ 11042065489383^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861134969 10000000000 11042065489383 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538910253/1000000000 : ℝ)^2161 ≤ (11119741014921/25000000000000 : ℝ)^1649 := by
    have hnat : (538910253 : ℕ)^2161*25000000000000^1649 ≤ 11119741014921^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538910253 1000000000 11119741014921 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389103119/10000000000 : ℝ)^2161 ≤ (44478970430391/100000000000000 : ℝ)^1649 := by
    have hnat : (5389103119 : ℕ)^2161*100000000000000^1649 ≤ 44478970430391^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389103119 10000000000 44478970430391 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1861134969/10000000000 : ℝ), (538910253/1000000000 : ℝ), (5389103119/10000000000 : ℝ)] ![(11042065489383/100000000000000 : ℝ), (11119741014921/25000000000000 : ℝ), (44478970430391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1861134969/10000000000 : ℝ)|^2161 ≤ (11042065489383/100000000000000 : ℝ)^1649
        have hw : |(-1861134969/10000000000 : ℝ)|=(1861134969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538910253/1000000000 : ℝ)|^2161 ≤ (11119741014921/25000000000000 : ℝ)^1649
        have hw : |(538910253/1000000000 : ℝ)|=(538910253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389103119/10000000000 : ℝ)|^2161 ≤ (44478970430391/100000000000000 : ℝ)^1649
        have hw : |(5389103119/10000000000 : ℝ)|=(5389103119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_1 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642711731/5000000000 : ℝ)*x 0 + (-2003276937/10000000000 : ℝ)*x 1 + (269455123/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642711731/5000000000 : ℝ)^2161 ≤ (10840230232019/25000000000000 : ℝ)^1649 := by
    have hnat : (2642711731 : ℕ)^2161*25000000000000^1649 ≤ 10840230232019^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642711731 5000000000 10840230232019 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003276937/10000000000 : ℝ)^2161 ≤ (243202314971/2000000000000 : ℝ)^1649 := by
    have hnat : (2003276937 : ℕ)^2161*2000000000000^1649 ≤ 243202314971^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003276937 10000000000 243202314971 2000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269455123/500000000 : ℝ)^2161 ≤ (8895792660511/20000000000000 : ℝ)^1649 := by
    have hnat : (269455123 : ℕ)^2161*20000000000000^1649 ≤ 8895792660511^1649*500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269455123 500000000 8895792660511 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642711731/5000000000 : ℝ), (-2003276937/10000000000 : ℝ), (269455123/500000000 : ℝ)] ![(10840230232019/25000000000000 : ℝ), (243202314971/2000000000000 : ℝ), (8895792660511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642711731/5000000000 : ℝ)|^2161 ≤ (10840230232019/25000000000000 : ℝ)^1649
        have hw : |(2642711731/5000000000 : ℝ)|=(2642711731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003276937/10000000000 : ℝ)|^2161 ≤ (243202314971/2000000000000 : ℝ)^1649
        have hw : |(-2003276937/10000000000 : ℝ)|=(2003276937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269455123/500000000 : ℝ)|^2161 ≤ (8895792660511/20000000000000 : ℝ)^1649
        have hw : |(269455123/500000000 : ℝ)|=(269455123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_2 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (528542327/1000000000 : ℝ)*x 0 + (269455131/500000000 : ℝ)*x 1 + (-100163849/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528542327/1000000000 : ℝ)^2161 ≤ (8672183772773/20000000000000 : ℝ)^1649 := by
    have hnat : (528542327 : ℕ)^2161*20000000000000^1649 ≤ 8672183772773^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528542327 1000000000 8672183772773 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269455131/500000000 : ℝ)^2161 ≤ (44478965033137/100000000000000 : ℝ)^1649 := by
    have hnat : (269455131 : ℕ)^2161*100000000000000^1649 ≤ 44478965033137^1649*500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269455131 500000000 44478965033137 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100163849/500000000 : ℝ)^2161 ≤ (12160116090607/100000000000000 : ℝ)^1649 := by
    have hnat : (100163849 : ℕ)^2161*100000000000000^1649 ≤ 12160116090607^1649*500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100163849 500000000 12160116090607 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528542327/1000000000 : ℝ), (269455131/500000000 : ℝ), (-100163849/500000000 : ℝ)] ![(8672183772773/20000000000000 : ℝ), (44478965033137/100000000000000 : ℝ), (12160116090607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528542327/1000000000 : ℝ)|^2161 ≤ (8672183772773/20000000000000 : ℝ)^1649
        have hw : |(528542327/1000000000 : ℝ)|=(528542327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269455131/500000000 : ℝ)|^2161 ≤ (44478965033137/100000000000000 : ℝ)^1649
        have hw : |(269455131/500000000 : ℝ)|=(269455131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100163849/500000000 : ℝ)|^2161 ≤ (12160116090607/100000000000000 : ℝ)^1649
        have hw : |(-100163849/500000000 : ℝ)|=(100163849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_3 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (89382973/200000000 : ℝ)*x 0 + (1062849979/2500000000 : ℝ)*x 1 + (4251400171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89382973/200000000 : ℝ)^2161 ≤ (17401740200033/50000000000000 : ℝ)^1649 := by
    have hnat : (89382973 : ℕ)^2161*50000000000000^1649 ≤ 17401740200033^1649*200000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89382973 200000000 17401740200033 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062849979/2500000000 : ℝ)^2161 ≤ (8149564627843/25000000000000 : ℝ)^1649 := by
    have hnat : (1062849979 : ℕ)^2161*25000000000000^1649 ≤ 8149564627843^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062849979 2500000000 8149564627843 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251400171/10000000000 : ℝ)^2161 ≤ (2037391317107/6250000000000 : ℝ)^1649 := by
    have hnat : (4251400171 : ℕ)^2161*6250000000000^1649 ≤ 2037391317107^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251400171 10000000000 2037391317107 6250000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89382973/200000000 : ℝ), (1062849979/2500000000 : ℝ), (4251400171/10000000000 : ℝ)] ![(17401740200033/50000000000000 : ℝ), (8149564627843/25000000000000 : ℝ), (2037391317107/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89382973/200000000 : ℝ)|^2161 ≤ (17401740200033/50000000000000 : ℝ)^1649
        have hw : |(89382973/200000000 : ℝ)|=(89382973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062849979/2500000000 : ℝ)|^2161 ≤ (8149564627843/25000000000000 : ℝ)^1649
        have hw : |(1062849979/2500000000 : ℝ)|=(1062849979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251400171/10000000000 : ℝ)|^2161 ≤ (2037391317107/6250000000000 : ℝ)^1649
        have hw : |(4251400171/10000000000 : ℝ)|=(4251400171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_4 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-548813139/2500000000 : ℝ)*x 0 + (5265351897/10000000000 : ℝ)*x 1 + (1053070357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548813139/2500000000 : ℝ)^2161 ≤ (2741897478791/20000000000000 : ℝ)^1649 := by
    have hnat : (548813139 : ℕ)^2161*20000000000000^1649 ≤ 2741897478791^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548813139 2500000000 2741897478791 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265351897/10000000000 : ℝ)^2161 ≤ (2157262844843/5000000000000 : ℝ)^1649 := by
    have hnat : (5265351897 : ℕ)^2161*5000000000000^1649 ≤ 2157262844843^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265351897 10000000000 2157262844843 5000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053070357/2000000000 : ℝ)^2161 ≤ (21572627847079/50000000000000 : ℝ)^1649 := by
    have hnat : (1053070357 : ℕ)^2161*50000000000000^1649 ≤ 21572627847079^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053070357 2000000000 21572627847079 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548813139/2500000000 : ℝ), (5265351897/10000000000 : ℝ), (1053070357/2000000000 : ℝ)] ![(2741897478791/20000000000000 : ℝ), (2157262844843/5000000000000 : ℝ), (21572627847079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548813139/2500000000 : ℝ)|^2161 ≤ (2741897478791/20000000000000 : ℝ)^1649
        have hw : |(-548813139/2500000000 : ℝ)|=(548813139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265351897/10000000000 : ℝ)|^2161 ≤ (2157262844843/5000000000000 : ℝ)^1649
        have hw : |(5265351897/10000000000 : ℝ)|=(5265351897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053070357/2000000000 : ℝ)|^2161 ≤ (21572627847079/50000000000000 : ℝ)^1649
        have hw : |(1053070357/2000000000 : ℝ)|=(1053070357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_5 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686135067/5000000000 : ℝ)*x 0 + (-1026536393/5000000000 : ℝ)*x 1 + (1316337953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686135067/5000000000 : ℝ)^2161 ≤ (1384280963763/3125000000000 : ℝ)^1649 := by
    have hnat : (2686135067 : ℕ)^2161*3125000000000^1649 ≤ 1384280963763^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686135067 5000000000 1384280963763 3125000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026536393/5000000000 : ℝ)^2161 ≤ (12557753157541/100000000000000 : ℝ)^1649 := by
    have hnat : (1026536393 : ℕ)^2161*100000000000000^1649 ≤ 12557753157541^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026536393 5000000000 12557753157541 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316337953/2500000000 : ℝ)^2161 ≤ (8629051196819/20000000000000 : ℝ)^1649 := by
    have hnat : (1316337953 : ℕ)^2161*20000000000000^1649 ≤ 8629051196819^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316337953 2500000000 8629051196819 20000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686135067/5000000000 : ℝ), (-1026536393/5000000000 : ℝ), (1316337953/2500000000 : ℝ)] ![(1384280963763/3125000000000 : ℝ), (12557753157541/100000000000000 : ℝ), (8629051196819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686135067/5000000000 : ℝ)|^2161 ≤ (1384280963763/3125000000000 : ℝ)^1649
        have hw : |(2686135067/5000000000 : ℝ)|=(2686135067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026536393/5000000000 : ℝ)|^2161 ≤ (12557753157541/100000000000000 : ℝ)^1649
        have hw : |(-1026536393/5000000000 : ℝ)|=(1026536393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316337953/2500000000 : ℝ)|^2161 ≤ (8629051196819/20000000000000 : ℝ)^1649
        have hw : |(1316337953/2500000000 : ℝ)|=(1316337953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_6 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686135079/5000000000 : ℝ)*x 0 + (5265351849/10000000000 : ℝ)*x 1 + (-32079261/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686135079/5000000000 : ℝ)^2161 ≤ (44296991099751/100000000000000 : ℝ)^1649 := by
    have hnat : (2686135079 : ℕ)^2161*100000000000000^1649 ≤ 44296991099751^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686135079 5000000000 44296991099751 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265351849/10000000000 : ℝ)^2161 ≤ (5393157047677/12500000000000 : ℝ)^1649 := by
    have hnat : (5265351849 : ℕ)^2161*12500000000000^1649 ≤ 5393157047677^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265351849 10000000000 5393157047677 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32079261/156250000 : ℝ)^2161 ≤ (12557752500253/100000000000000 : ℝ)^1649 := by
    have hnat : (32079261 : ℕ)^2161*100000000000000^1649 ≤ 12557752500253^1649*156250000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32079261 156250000 12557752500253 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686135079/5000000000 : ℝ), (5265351849/10000000000 : ℝ), (-32079261/156250000 : ℝ)] ![(44296991099751/100000000000000 : ℝ), (5393157047677/12500000000000 : ℝ), (12557752500253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686135079/5000000000 : ℝ)|^2161 ≤ (44296991099751/100000000000000 : ℝ)^1649
        have hw : |(2686135079/5000000000 : ℝ)|=(2686135079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265351849/10000000000 : ℝ)|^2161 ≤ (5393157047677/12500000000000 : ℝ)^1649
        have hw : |(5265351849/10000000000 : ℝ)|=(5265351849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32079261/156250000 : ℝ)|^2161 ≤ (12557752500253/100000000000000 : ℝ)^1649
        have hw : |(-32079261/156250000 : ℝ)|=(32079261/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_7 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (208636763/500000000 : ℝ)*x 0 + (4399553931/10000000000 : ℝ)*x 1 + (54994421/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208636763/500000000 : ℝ)^2161 ≤ (31810085589967/100000000000000 : ℝ)^1649 := by
    have hnat : (208636763 : ℕ)^2161*100000000000000^1649 ≤ 31810085589967^1649*500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208636763 500000000 31810085589967 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4399553931/10000000000 : ℝ)^2161 ≤ (8523739619279/25000000000000 : ℝ)^1649 := by
    have hnat : (4399553931 : ℕ)^2161*25000000000000^1649 ≤ 8523739619279^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399553931 10000000000 8523739619279 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54994421/125000000 : ℝ)^2161 ≤ (34094955928001/100000000000000 : ℝ)^1649 := by
    have hnat : (54994421 : ℕ)^2161*100000000000000^1649 ≤ 34094955928001^1649*125000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54994421 125000000 34094955928001 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208636763/500000000 : ℝ), (4399553931/10000000000 : ℝ), (54994421/125000000 : ℝ)] ![(31810085589967/100000000000000 : ℝ), (8523739619279/25000000000000 : ℝ), (34094955928001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208636763/500000000 : ℝ)|^2161 ≤ (31810085589967/100000000000000 : ℝ)^1649
        have hw : |(208636763/500000000 : ℝ)|=(208636763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4399553931/10000000000 : ℝ)|^2161 ≤ (8523739619279/25000000000000 : ℝ)^1649
        have hw : |(4399553931/10000000000 : ℝ)|=(4399553931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54994421/125000000 : ℝ)|^2161 ≤ (34094955928001/100000000000000 : ℝ)^1649
        have hw : |(54994421/125000000 : ℝ)|=(54994421/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_8 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062518439/5000000000 : ℝ)*x 0 + (2590032181/5000000000 : ℝ)*x 1 + (5403113827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062518439/5000000000 : ℝ)^2161 ≤ (1642213765353/12500000000000 : ℝ)^1649 := by
    have hnat : (1062518439 : ℕ)^2161*12500000000000^1649 ≤ 1642213765353^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062518439 5000000000 1642213765353 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590032181/5000000000 : ℝ)^2161 ≤ (42231716506701/100000000000000 : ℝ)^1649 := by
    have hnat : (2590032181 : ℕ)^2161*100000000000000^1649 ≤ 42231716506701^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590032181 5000000000 42231716506701 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403113827/10000000000 : ℝ)^2161 ≤ (44630573352181/100000000000000 : ℝ)^1649 := by
    have hnat : (5403113827 : ℕ)^2161*100000000000000^1649 ≤ 44630573352181^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403113827 10000000000 44630573352181 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062518439/5000000000 : ℝ), (2590032181/5000000000 : ℝ), (5403113827/10000000000 : ℝ)] ![(1642213765353/12500000000000 : ℝ), (42231716506701/100000000000000 : ℝ), (44630573352181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062518439/5000000000 : ℝ)|^2161 ≤ (1642213765353/12500000000000 : ℝ)^1649
        have hw : |(-1062518439/5000000000 : ℝ)|=(1062518439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590032181/5000000000 : ℝ)|^2161 ≤ (42231716506701/100000000000000 : ℝ)^1649
        have hw : |(2590032181/5000000000 : ℝ)|=(2590032181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403113827/10000000000 : ℝ)|^2161 ≤ (44630573352181/100000000000000 : ℝ)^1649
        have hw : |(5403113827/10000000000 : ℝ)|=(5403113827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_9 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (527558517/1000000000 : ℝ)*x 0 + (-499377053/2500000000 : ℝ)*x 1 + (2701556937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527558517/1000000000 : ℝ)^2161 ≤ (43255179065267/100000000000000 : ℝ)^1649 := by
    have hnat : (527558517 : ℕ)^2161*100000000000000^1649 ≤ 43255179065267^1649*1000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527558517 1000000000 43255179065267 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499377053/2500000000 : ℝ)^2161 ≤ (6057123529071/50000000000000 : ℝ)^1649 := by
    have hnat : (499377053 : ℕ)^2161*50000000000000^1649 ≤ 6057123529071^1649*2500000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499377053 2500000000 6057123529071 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701556937/5000000000 : ℝ)^2161 ≤ (892611477219/2000000000000 : ℝ)^1649 := by
    have hnat : (2701556937 : ℕ)^2161*2000000000000^1649 ≤ 892611477219^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701556937 5000000000 892611477219 2000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527558517/1000000000 : ℝ), (-499377053/2500000000 : ℝ), (2701556937/5000000000 : ℝ)] ![(43255179065267/100000000000000 : ℝ), (6057123529071/50000000000000 : ℝ), (892611477219/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527558517/1000000000 : ℝ)|^2161 ≤ (43255179065267/100000000000000 : ℝ)^1649
        have hw : |(527558517/1000000000 : ℝ)|=(527558517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499377053/2500000000 : ℝ)|^2161 ≤ (6057123529071/50000000000000 : ℝ)^1649
        have hw : |(-499377053/2500000000 : ℝ)|=(499377053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701556937/5000000000 : ℝ)|^2161 ≤ (892611477219/2000000000000 : ℝ)^1649
        have hw : |(2701556937/5000000000 : ℝ)|=(2701556937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_10 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275585187/10000000000 : ℝ)*x 0 + (5403113847/10000000000 : ℝ)*x 1 + (-79900329/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275585187/10000000000 : ℝ)^2161 ≤ (4325517924793/10000000000000 : ℝ)^1649 := by
    have hnat : (5275585187 : ℕ)^2161*10000000000000^1649 ≤ 4325517924793^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275585187 10000000000 4325517924793 10000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403113847/10000000000 : ℝ)^2161 ≤ (22315286784339/50000000000000 : ℝ)^1649 := by
    have hnat : (5403113847 : ℕ)^2161*50000000000000^1649 ≤ 22315286784339^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403113847 10000000000 22315286784339 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79900329/400000000 : ℝ)^2161 ≤ (6057123580731/50000000000000 : ℝ)^1649 := by
    have hnat : (79900329 : ℕ)^2161*50000000000000^1649 ≤ 6057123580731^1649*400000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79900329 400000000 6057123580731 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275585187/10000000000 : ℝ), (5403113847/10000000000 : ℝ), (-79900329/400000000 : ℝ)] ![(4325517924793/10000000000000 : ℝ), (22315286784339/50000000000000 : ℝ), (6057123580731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275585187/10000000000 : ℝ)|^2161 ≤ (4325517924793/10000000000000 : ℝ)^1649
        have hw : |(5275585187/10000000000 : ℝ)|=(5275585187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403113847/10000000000 : ℝ)|^2161 ≤ (22315286784339/50000000000000 : ℝ)^1649
        have hw : |(5403113847/10000000000 : ℝ)|=(5403113847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79900329/400000000 : ℝ)|^2161 ≤ (6057123580731/50000000000000 : ℝ)^1649
        have hw : |(-79900329/400000000 : ℝ)|=(79900329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_11 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4502149081/10000000000 : ℝ)*x 0 + (846922491/2000000000 : ℝ)*x 1 + (2117306227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4502149081/10000000000 : ℝ)^2161 ≤ (8785162482947/25000000000000 : ℝ)^1649 := by
    have hnat : (4502149081 : ℕ)^2161*25000000000000^1649 ≤ 8785162482947^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502149081 10000000000 8785162482947 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846922491/2000000000 : ℝ)^2161 ≤ (64859350063/200000000000 : ℝ)^1649 := by
    have hnat : (846922491 : ℕ)^2161*200000000000^1649 ≤ 64859350063^1649*2000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846922491 2000000000 64859350063 200000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117306227/5000000000 : ℝ)^2161 ≤ (4053709377683/12500000000000 : ℝ)^1649 := by
    have hnat : (2117306227 : ℕ)^2161*12500000000000^1649 ≤ 4053709377683^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117306227 5000000000 4053709377683 12500000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4502149081/10000000000 : ℝ), (846922491/2000000000 : ℝ), (2117306227/5000000000 : ℝ)] ![(8785162482947/25000000000000 : ℝ), (64859350063/200000000000 : ℝ), (4053709377683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4502149081/10000000000 : ℝ)|^2161 ≤ (8785162482947/25000000000000 : ℝ)^1649
        have hw : |(4502149081/10000000000 : ℝ)|=(4502149081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846922491/2000000000 : ℝ)|^2161 ≤ (64859350063/200000000000 : ℝ)^1649
        have hw : |(846922491/2000000000 : ℝ)|=(846922491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117306227/5000000000 : ℝ)|^2161 ≤ (4053709377683/12500000000000 : ℝ)^1649
        have hw : |(2117306227/5000000000 : ℝ)|=(2117306227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_12 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931649697/10000000000 : ℝ)*x 0 + (5472229253/10000000000 : ℝ)*x 1 + (5254266621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931649697/10000000000 : ℝ)^2161 ≤ (2898380618601/25000000000000 : ℝ)^1649 := by
    have hnat : (1931649697 : ℕ)^2161*25000000000000^1649 ≤ 2898380618601^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931649697 10000000000 2898380618601 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472229253/10000000000 : ℝ)^2161 ≤ (11345054967723/25000000000000 : ℝ)^1649 := by
    have hnat : (5472229253 : ℕ)^2161*25000000000000^1649 ≤ 11345054967723^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472229253 10000000000 11345054967723 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254266621/10000000000 : ℝ)^2161 ≤ (43026257642067/100000000000000 : ℝ)^1649 := by
    have hnat : (5254266621 : ℕ)^2161*100000000000000^1649 ≤ 43026257642067^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254266621 10000000000 43026257642067 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931649697/10000000000 : ℝ), (5472229253/10000000000 : ℝ), (5254266621/10000000000 : ℝ)] ![(2898380618601/25000000000000 : ℝ), (11345054967723/25000000000000 : ℝ), (43026257642067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931649697/10000000000 : ℝ)|^2161 ≤ (2898380618601/25000000000000 : ℝ)^1649
        have hw : |(-1931649697/10000000000 : ℝ)|=(1931649697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472229253/10000000000 : ℝ)|^2161 ≤ (11345054967723/25000000000000 : ℝ)^1649
        have hw : |(5472229253/10000000000 : ℝ)|=(5472229253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254266621/10000000000 : ℝ)|^2161 ≤ (43026257642067/100000000000000 : ℝ)^1649
        have hw : |(5254266621/10000000000 : ℝ)|=(5254266621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_13 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5380047629/10000000000 : ℝ)*x 0 + (-2057430429/10000000000 : ℝ)*x 1 + (2627133197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380047629/10000000000 : ℝ)^2161 ≤ (44381050533347/100000000000000 : ℝ)^1649 := by
    have hnat : (5380047629 : ℕ)^2161*100000000000000^1649 ≤ 44381050533347^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380047629 10000000000 44381050533347 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057430429/10000000000 : ℝ)^2161 ≤ (12592694240809/100000000000000 : ℝ)^1649 := by
    have hnat : (2057430429 : ℕ)^2161*100000000000000^1649 ≤ 12592694240809^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057430429 10000000000 12592694240809 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627133197/5000000000 : ℝ)^2161 ≤ (10756563801511/25000000000000 : ℝ)^1649 := by
    have hnat : (2627133197 : ℕ)^2161*25000000000000^1649 ≤ 10756563801511^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627133197 5000000000 10756563801511 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380047629/10000000000 : ℝ), (-2057430429/10000000000 : ℝ), (2627133197/5000000000 : ℝ)] ![(44381050533347/100000000000000 : ℝ), (12592694240809/100000000000000 : ℝ), (10756563801511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380047629/10000000000 : ℝ)|^2161 ≤ (44381050533347/100000000000000 : ℝ)^1649
        have hw : |(5380047629/10000000000 : ℝ)|=(5380047629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057430429/10000000000 : ℝ)|^2161 ≤ (12592694240809/100000000000000 : ℝ)^1649
        have hw : |(-2057430429/10000000000 : ℝ)|=(2057430429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627133197/5000000000 : ℝ)|^2161 ≤ (10756563801511/25000000000000 : ℝ)^1649
        have hw : |(2627133197/5000000000 : ℝ)|=(2627133197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_14 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5380047753/10000000000 : ℝ)*x 0 + (5254266879/10000000000 : ℝ)*x 1 + (-1028714807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380047753/10000000000 : ℝ)^2161 ≤ (44381051873849/100000000000000 : ℝ)^1649 := by
    have hnat : (5380047753 : ℕ)^2161*100000000000000^1649 ≤ 44381051873849^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380047753 10000000000 44381051873849 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254266879/10000000000 : ℝ)^2161 ≤ (43026260410763/100000000000000 : ℝ)^1649 := by
    have hnat : (5254266879 : ℕ)^2161*100000000000000^1649 ≤ 43026260410763^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254266879 10000000000 43026260410763 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028714807/5000000000 : ℝ)^2161 ≤ (3148171925927/25000000000000 : ℝ)^1649 := by
    have hnat : (1028714807 : ℕ)^2161*25000000000000^1649 ≤ 3148171925927^1649*5000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028714807 5000000000 3148171925927 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380047753/10000000000 : ℝ), (5254266879/10000000000 : ℝ), (-1028714807/5000000000 : ℝ)] ![(44381051873849/100000000000000 : ℝ), (43026260410763/100000000000000 : ℝ), (3148171925927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380047753/10000000000 : ℝ)|^2161 ≤ (44381051873849/100000000000000 : ℝ)^1649
        have hw : |(5380047753/10000000000 : ℝ)|=(5380047753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254266879/10000000000 : ℝ)|^2161 ≤ (43026260410763/100000000000000 : ℝ)^1649
        have hw : |(5254266879/10000000000 : ℝ)|=(5254266879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028714807/5000000000 : ℝ)|^2161 ≤ (3148171925927/25000000000000 : ℝ)^1649
        have hw : |(-1028714807/5000000000 : ℝ)|=(1028714807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1362_box_15 (p : ℝ) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4145735599/10000000000 : ℝ)*x 0 + (4412814289/10000000000 : ℝ)*x 1 + (4412813757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145735599/10000000000 : ℝ)^2161 ≤ (7885155622399/25000000000000 : ℝ)^1649 := by
    have hnat : (4145735599 : ℕ)^2161*25000000000000^1649 ≤ 7885155622399^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145735599 10000000000 7885155622399 25000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412814289/10000000000 : ℝ)^2161 ≤ (17114845726907/50000000000000 : ℝ)^1649 := by
    have hnat : (4412814289 : ℕ)^2161*50000000000000^1649 ≤ 17114845726907^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412814289 10000000000 17114845726907 50000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412813757/10000000000 : ℝ)^2161 ≤ (34229686045859/100000000000000 : ℝ)^1649 := by
    have hnat : (4412813757 : ℕ)^2161*100000000000000^1649 ≤ 34229686045859^1649*10000000000^2161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412813757 10000000000 34229686045859 100000000000000 2161 1649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2161/512 : ℝ)) 2161 1649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145735599/10000000000 : ℝ), (4412814289/10000000000 : ℝ), (4412813757/10000000000 : ℝ)] ![(7885155622399/25000000000000 : ℝ), (17114845726907/50000000000000 : ℝ), (34229686045859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145735599/10000000000 : ℝ)|^2161 ≤ (7885155622399/25000000000000 : ℝ)^1649
        have hw : |(4145735599/10000000000 : ℝ)|=(4145735599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412814289/10000000000 : ℝ)|^2161 ≤ (17114845726907/50000000000000 : ℝ)^1649
        have hw : |(4412814289/10000000000 : ℝ)|=(4412814289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412813757/10000000000 : ℝ)|^2161 ≤ (34229686045859/100000000000000 : ℝ)^1649
        have hw : |(4412813757/10000000000 : ℝ)|=(4412813757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1362_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3929/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2949/5000 : ℝ) ∧ (80071/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8443/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2799/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2799/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2799/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2799/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2799/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2799/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2799/25000 : ℝ) ^ (4321/1024 : ℝ) ≤ (9711927166416371/100000000000000000000 : ℝ) := by
    have hpowers : (2799/25000 : ℝ)^4321 ≤ (9711927166416371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2799 : ℕ)^4321*100000000000000000000^1024 ≤ 9711927166416371^1024*25000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 25000 9711927166416371 100000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/25000 : ℝ)) (X := (9711927166416371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14719/100000 : ℝ) ^ (4321/1024 : ℝ) ≤ (15404371578617491/50000000000000000000 : ℝ) := by
    have hpowers : (14719/100000 : ℝ)^4321 ≤ (15404371578617491/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14719 : ℕ)^4321*50000000000000000000^1024 ≤ 15404371578617491^1024*100000^4321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14719 100000 15404371578617491 50000000000000000000 4321 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14719/100000 : ℝ)) (X := (15404371578617491/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009711927166416371/50000000000000000000 : ℝ) ≤ (2500115069156907/2500000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (50009711927166416371/50000000000000000000 : ℝ)^1024 ≤ (2500115069156907/2500000000000000 : ℝ)^4321 := by
      have hnat : (50009711927166416371 : ℕ)^1024*2500000000000000^4321 ≤ 2500115069156907^4321*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009711927166416371 50000000000000000000 2500115069156907 2500000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500115069156907/2500000000000000 : ℝ)) (X := (50009711927166416371/50000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040520670323651353/100000000000000000000 : ℝ) ≤ (10000960119266633/10000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (100040520670323651353/100000000000000000000 : ℝ)^1024 ≤ (10000960119266633/10000000000000000 : ℝ)^4321 := by
      have hnat : (100040520670323651353 : ℕ)^1024*10000000000000000^4321 ≤ 10000960119266633^4321*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040520670323651353 100000000000000000000 10000960119266633 10000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000960119266633/10000000000000000 : ℝ)) (X := (100040520670323651353/100000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015404371578617491/25000000000000000000 : ℝ) ≤ (5000729980952819/5000000000000000 : ℝ) ^ (4321/1024 : ℝ) := by
    have hpowers : (25015404371578617491/25000000000000000000 : ℝ)^1024 ≤ (5000729980952819/5000000000000000 : ℝ)^4321 := by
      have hnat : (25015404371578617491 : ℕ)^1024*5000000000000000^4321 ≤ 5000729980952819^4321*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015404371578617491 25000000000000000000 5000729980952819 5000000000000000 1024 4321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000729980952819/5000000000000000 : ℝ)) (X := (25015404371578617491/25000000000000000000 : ℝ)) (by norm_num) 4321 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9711927166416371/100000000000000000000 : ℝ) ≤ ((8805107269546633371/8807500000000000000 : ℝ)+2*(99968527801/70460000000000 : ℝ)*(2799/25000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (8805107269546633371/8807500000000000000 : ℝ)+2*(99968527801/70460000000000 : ℝ)*(2799/25000 : ℝ)=(2500115069156907/2500000000000000 : ℝ) by norm_num, show 1+2*(9711927166416371/100000000000000000000 : ℝ)=(50009711927166416371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15404371578617491/50000000000000000000 : ℝ)+(9711927166416371/100000000000000000000 : ℝ) ≤ ((8805107269546633371/8807500000000000000 : ℝ)+(99968527801/70460000000000 : ℝ)*((14719/100000 : ℝ)+(2799/25000 : ℝ)))^(4321/1024 : ℝ) := by
    rw [show (8805107269546633371/8807500000000000000 : ℝ)+(99968527801/70460000000000 : ℝ)*((14719/100000 : ℝ)+(2799/25000 : ℝ))=(10000960119266633/10000000000000000 : ℝ) by norm_num, show 1+(15404371578617491/50000000000000000000 : ℝ)+(9711927166416371/100000000000000000000 : ℝ)=(100040520670323651353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15404371578617491/50000000000000000000 : ℝ) ≤ ((8805107269546633371/8807500000000000000 : ℝ)+2*(99968527801/70460000000000 : ℝ)*(14719/100000 : ℝ))^(4321/1024 : ℝ) := by
    rw [show (8805107269546633371/8807500000000000000 : ℝ)+2*(99968527801/70460000000000 : ℝ)*(14719/100000 : ℝ)=(5000729980952819/5000000000000000 : ℝ) by norm_num, show 1+2*(15404371578617491/50000000000000000000 : ℝ)=(25015404371578617491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8805107269546633371/8807500000000000000 : ℝ)*(X 1 0+X 2 0)+(99968527801/70460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (8805107269546633371/8807500000000000000 : ℝ)) (alpha := (99968527801/70460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8805107269546633371/8807500000000000000 : ℝ)*(X 0 1+X 2 1)+(99968527801/70460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (8805107269546633371/8807500000000000000 : ℝ)) (alpha := (99968527801/70460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8805107269546633371/8807500000000000000 : ℝ)*(X 0 2+X 1 2)+(99968527801/70460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4321/1024 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (8805107269546633371/8807500000000000000 : ℝ)) (alpha := (99968527801/70460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1861134969/10000000000 : ℝ)*X 0 0+(538910253/1000000000 : ℝ)*X 0 1+(5389103119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642711731/5000000000 : ℝ)*X 1 0+(-2003276937/10000000000 : ℝ)*X 1 1+(269455123/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((528542327/1000000000 : ℝ)*X 2 0+(269455131/500000000 : ℝ)*X 2 1+(-100163849/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((89382973/200000000 : ℝ)*X 0 0+(1062849979/2500000000 : ℝ)*X 0 1+(4251400171/10000000000 : ℝ)*X 0 2+(89382973/200000000 : ℝ)*X 1 0+(1062849979/2500000000 : ℝ)*X 1 1+(4251400171/10000000000 : ℝ)*X 1 2+(89382973/200000000 : ℝ)*X 2 0+(1062849979/2500000000 : ℝ)*X 2 1+(4251400171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548813139/2500000000 : ℝ)*X 0 0+(5265351897/10000000000 : ℝ)*X 0 1+(1053070357/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686135067/5000000000 : ℝ)*X 1 0+(-1026536393/5000000000 : ℝ)*X 1 1+(1316337953/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686135079/5000000000 : ℝ)*X 2 0+(5265351849/10000000000 : ℝ)*X 2 1+(-32079261/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((208636763/500000000 : ℝ)*X 0 0+(4399553931/10000000000 : ℝ)*X 0 1+(54994421/125000000 : ℝ)*X 0 2+(208636763/500000000 : ℝ)*X 1 0+(4399553931/10000000000 : ℝ)*X 1 1+(54994421/125000000 : ℝ)*X 1 2+(208636763/500000000 : ℝ)*X 2 0+(4399553931/10000000000 : ℝ)*X 2 1+(54994421/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1062518439/5000000000 : ℝ)*X 0 0+(2590032181/5000000000 : ℝ)*X 0 1+(5403113827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527558517/1000000000 : ℝ)*X 1 0+(-499377053/2500000000 : ℝ)*X 1 1+(2701556937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275585187/10000000000 : ℝ)*X 2 0+(5403113847/10000000000 : ℝ)*X 2 1+(-79900329/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4502149081/10000000000 : ℝ)*X 0 0+(846922491/2000000000 : ℝ)*X 0 1+(2117306227/5000000000 : ℝ)*X 0 2+(4502149081/10000000000 : ℝ)*X 1 0+(846922491/2000000000 : ℝ)*X 1 1+(2117306227/5000000000 : ℝ)*X 1 2+(4502149081/10000000000 : ℝ)*X 2 0+(846922491/2000000000 : ℝ)*X 2 1+(2117306227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1931649697/10000000000 : ℝ)*X 0 0+(5472229253/10000000000 : ℝ)*X 0 1+(5254266621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380047629/10000000000 : ℝ)*X 1 0+(-2057430429/10000000000 : ℝ)*X 1 1+(2627133197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380047753/10000000000 : ℝ)*X 2 0+(5254266879/10000000000 : ℝ)*X 2 1+(-1028714807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4145735599/10000000000 : ℝ)*X 0 0+(4412814289/10000000000 : ℝ)*X 0 1+(4412813757/10000000000 : ℝ)*X 0 2+(4145735599/10000000000 : ℝ)*X 1 0+(4412814289/10000000000 : ℝ)*X 1 1+(4412813757/10000000000 : ℝ)*X 1 2+(4145735599/10000000000 : ℝ)*X 2 0+(4412814289/10000000000 : ℝ)*X 2 1+(4412813757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1362_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3929/6250 : ℝ) ≤ (-27682507326419756295893872498119/44037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92807/4000000000000 : ℝ)*(lower0) + (5401703/20000000000000 : ℝ)*(upper1) + (35605137/100000000000000 : ℝ)*(lower2) + (294294414805437/10000000000000 : ℝ)*(major0) + (294294414805437/10000000000000 : ℝ)*(major1) + (294294414805437/10000000000000 : ℝ)*(major2) + (1755200421/100000000000000 : ℝ)*(sp1) + (13269513/800000000000 : ℝ)*(sp3) + (1003619698702141/25000000000000 : ℝ)*(sp4) + (2007240681805193/50000000000000 : ℝ)*(sp5) + (2007234663285141/50000000000000 : ℝ)*(sp6) + (1892357256768641/100000000000000 : ℝ)*(sp7) + (2162001121/50000000000000 : ℝ)*(sp8) + (551689621/4000000000000 : ℝ)*(sp14) + (946179457728883/50000000000000 : ℝ)*(f.failure) + (2007241559405403/50000000000000 : ℝ)*(f.sum) + (558847821009/176150000000000000000000000 : ℝ)*base66 + (141251920928338127/88075000000000000000000000000000 : ℝ)*base67 + (21681486970611873/88075000000000000000000000000000 : ℝ)*base70 + (480792330037136873/88075000000000000000000000000000 : ℝ)*base72 + (3949906050201/220187500000000000000000000 : ℝ)*base73 + (943947242770961873/88075000000000000000000000000000 : ℝ)*base76 + (573653823601261873/88075000000000000000000000000000 : ℝ)*base78 + (1403835460596763127/88075000000000000000000000000000 : ℝ)*base79 + (12421479164801/3523000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17425207/5000000000000000000000 : ℝ)*base89 + (17425207/5000000000000000000000 : ℝ)*base91 + (17425207/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2949/5000 : ℝ) ≤ (64936203165512604147652373630769/110093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3385907/100000000000000 : ℝ)*(lower0) + (22544629/20000000000000 : ℝ)*(lower1) + (376117/6250000000000 : ℝ)*(lower3) + (16156617/12500000000000 : ℝ)*(lower5) + (1506155467892363/50000000000000 : ℝ)*(major0) + (1506155467892363/50000000000000 : ℝ)*(major1) + (1506155467892363/50000000000000 : ℝ)*(major2) + (2033989302285771/50000000000000 : ℝ)*(sp0) + (16271675044641/400000000000 : ℝ)*(sp1) + (406799815051387/10000000000000 : ℝ)*(sp2) + (968476967077691/50000000000000 : ℝ)*(sp3) + (8906009887/100000000000000 : ℝ)*(sp7) + (3969467681/5000000000000 : ℝ)*(sp9) + (2443242791/12500000000000 : ℝ)*(sp12) + (193696284016527/10000000000000 : ℝ)*(f.failure) + (406799815051387/10000000000000 : ℝ)*(f.sum) + (42450480723/13761718750000000000000000 : ℝ)*base65 + (3901017721930154327/440375000000000000000000000000000 : ℝ)*base68 + (3380094485923279327/440375000000000000000000000000000 : ℝ)*base70 + (1432480187735279327/440375000000000000000000000000000 : ℝ)*base72 + (22410577314589/3523000000000000000000000000 : ℝ)*base73 + (4785360040918529327/440375000000000000000000000000000 : ℝ)*base76 + (422327755485279327/440375000000000000000000000000000 : ℝ)*base78 + (558828497996345673/440375000000000000000000000000000 : ℝ)*base79 + (176703998319/88075000000000000000000000 : ℝ)*base82 + (9243683/1000000000000000000000 : ℝ)*base89 + (9243683/1000000000000000000000 : ℝ)*base91 + (9243683/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80071/100000 : ℝ) ≤ (17631096461028801037605921380937/22018750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2001969/100000000000000 : ℝ)*(upper0) + (752773/20000000000000 : ℝ)*(upper3) + (160991/50000000000000 : ℝ)*(upper4) + (166177353183349/5000000000000 : ℝ)*(major0) + (166177353183349/5000000000000 : ℝ)*(major1) + (166177353183349/5000000000000 : ℝ)*(major2) + (7389963/2500000000000 : ℝ)*(sp0) + (3162037743/25000000000000 : ℝ)*(sp1) + (5228634359/100000000000000 : ℝ)*(sp2) + (155193533/20000000000000 : ℝ)*(sp3) + (2241655140109727/50000000000000 : ℝ)*(sp8) + (2241648963833501/50000000000000 : ℝ)*(sp9) + (896661069436723/20000000000000 : ℝ)*(sp10) + (534272935268087/25000000000000 : ℝ)*(sp11) + (534273129260003/25000000000000 : ℝ)*(f.failure) + (2241655287908987/50000000000000 : ℝ)*(f.sum) + (9915285655389/1761500000000000000000000000 : ℝ)*base66 + (333907228909485521/44037500000000000000000000000000 : ℝ)*base68 + (233154735844376979/44037500000000000000000000000000 : ℝ)*base69 + (359564155203510521/44037500000000000000000000000000 : ℝ)*base72 + (2533708458477/110093750000000000000000000 : ℝ)*base73 + (295700520570498021/44037500000000000000000000000000 : ℝ)*base76 + (186354958799923021/44037500000000000000000000000000 : ℝ)*base78 + (257684463579876979/44037500000000000000000000000000 : ℝ)*base79 + (224373484551/880750000000000000000000000 : ℝ)*base81 + (12908313/2500000000000000000000 : ℝ)*base90 + (12908313/2500000000000000000000 : ℝ)*base92 + (12908313/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-8443/10000 : ℝ) ≤ (-371796494433290100925115447960733/440375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174623793/100000000000000 : ℝ)*(lower0) + (253331091/100000000000000 : ℝ)*(lower1) + (23663141/6250000000000 : ℝ)*(lower2) + (3360250998393247/100000000000000 : ℝ)*(major0) + (3360250998393247/100000000000000 : ℝ)*(major1) + (3360250998393247/100000000000000 : ℝ)*(major2) + (15517133243/100000000000000 : ℝ)*(sp0) + (255608386651/50000000000000 : ℝ)*(sp5) + (97560907941/100000000000000 : ℝ)*(sp6) + (16297440693/25000000000000 : ℝ)*(sp7) + (2293967588550577/50000000000000 : ℝ)*(sp12) + (917487895492219/20000000000000 : ℝ)*(sp13) + (573481641665807/12500000000000 : ℝ)*(sp14) + (2160628528869037/100000000000000 : ℝ)*(sp15) + (216069371863181/10000000000000 : ℝ)*(f.failure) + (4587950694234397/100000000000000 : ℝ)*(f.sum) + (12698876513053/3523000000000000000000000000 : ℝ)*base65 + (13185143911529370637/880750000000000000000000000000000 : ℝ)*base67 + (10253110125182120637/880750000000000000000000000000000 : ℝ)*base69 + (8257034177062620637/880750000000000000000000000000000 : ℝ)*base71 + (13342234851007/3523000000000000000000000000 : ℝ)*base74 + (12378184515214870637/880750000000000000000000000000000 : ℝ)*base75 + (13048206881455370637/880750000000000000000000000000000 : ℝ)*base77 + (42019911607513620637/880750000000000000000000000000000 : ℝ)*base79 + (1193068477909/880750000000000000000000000 : ℝ)*base82 + (6245449/1000000000000000000000 : ℝ)*base89 + (6245449/1000000000000000000000 : ℝ)*base91 + (6245449/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1362_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3929/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(2949/5000 : ℝ) else (80071/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8443/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1362_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1362_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3929/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(2949/5000 : ℝ) else (80071/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8443/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1362_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1362_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1362_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4321/1024 : ℝ) ≤ p) (hpb : p ≤ (2161/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155517229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3929/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(2949/5000 : ℝ) else (80071/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8443/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1362_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
