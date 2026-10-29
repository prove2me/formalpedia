-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:13.241374+00:00
-- url     : https://prove2.me/submissions/028abd5d-c637-41c2-86f2-0dda5d70f02c

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
theorem support_rectangle_w1384_s3_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-501714827/2500000000 : ℝ)*x 0 + (5422099523/10000000000 : ℝ)*x 1 + (327197163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501714827/2500000000 : ℝ)^543 ≤ (12228962630191/100000000000000 : ℝ)^415 := by
    have hnat : (501714827 : ℕ)^543*100000000000000^415 ≤ 12228962630191^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501714827 2500000000 12228962630191 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422099523/10000000000 : ℝ)^543 ≤ (22446352230683/50000000000000 : ℝ)^415 := by
    have hnat : (5422099523 : ℕ)^543*50000000000000^415 ≤ 22446352230683^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422099523 10000000000 22446352230683 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327197163/625000000 : ℝ)^543 ≤ (10719583223979/25000000000000 : ℝ)^415 := by
    have hnat : (327197163 : ℕ)^543*25000000000000^415 ≤ 10719583223979^415*625000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327197163 625000000 10719583223979 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501714827/2500000000 : ℝ), (5422099523/10000000000 : ℝ), (327197163/625000000 : ℝ)] ![(12228962630191/100000000000000 : ℝ), (22446352230683/50000000000000 : ℝ), (10719583223979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501714827/2500000000 : ℝ)|^543 ≤ (12228962630191/100000000000000 : ℝ)^415
        have hw : |(-501714827/2500000000 : ℝ)|=(501714827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422099523/10000000000 : ℝ)|^543 ≤ (22446352230683/50000000000000 : ℝ)^415
        have hw : |(5422099523/10000000000 : ℝ)|=(5422099523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327197163/625000000 : ℝ)|^543 ≤ (10719583223979/25000000000000 : ℝ)^415
        have hw : |(327197163/625000000 : ℝ)|=(327197163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (535119881/1000000000 : ℝ)*x 0 + (-131394179/625000000 : ℝ)*x 1 + (5235154981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535119881/1000000000 : ℝ)^543 ≤ (22063085350617/50000000000000 : ℝ)^415 := by
    have hnat : (535119881 : ℕ)^543*50000000000000^415 ≤ 22063085350617^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535119881 1000000000 22063085350617 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131394179/625000000 : ℝ)^543 ≤ (519819695601/4000000000000 : ℝ)^415 := by
    have hnat : (131394179 : ℕ)^543*4000000000000^415 ≤ 519819695601^415*625000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131394179 625000000 519819695601 4000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235154981/10000000000 : ℝ)^543 ≤ (10719584223309/25000000000000 : ℝ)^415 := by
    have hnat : (5235154981 : ℕ)^543*25000000000000^415 ≤ 10719584223309^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235154981 10000000000 10719584223309 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535119881/1000000000 : ℝ), (-131394179/625000000 : ℝ), (5235154981/10000000000 : ℝ)] ![(22063085350617/50000000000000 : ℝ), (519819695601/4000000000000 : ℝ), (10719584223309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535119881/1000000000 : ℝ)|^543 ≤ (22063085350617/50000000000000 : ℝ)^415
        have hw : |(535119881/1000000000 : ℝ)|=(535119881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131394179/625000000 : ℝ)|^543 ≤ (519819695601/4000000000000 : ℝ)^415
        have hw : |(-131394179/625000000 : ℝ)|=(131394179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235154981/10000000000 : ℝ)|^543 ≤ (10719584223309/25000000000000 : ℝ)^415
        have hw : |(5235154981/10000000000 : ℝ)|=(5235154981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (167224963/312500000 : ℝ)*x 0 + (654394379/1250000000 : ℝ)*x 1 + (-2102306789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167224963/312500000 : ℝ)^543 ≤ (4412617076597/10000000000000 : ℝ)^415 := by
    have hnat : (167224963 : ℕ)^543*10000000000000^415 ≤ 4412617076597^415*312500000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167224963 312500000 4412617076597 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654394379/1250000000 : ℝ)^543 ≤ (21439168719893/50000000000000 : ℝ)^415 := by
    have hnat : (654394379 : ℕ)^543*50000000000000^415 ≤ 21439168719893^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654394379 1250000000 21439168719893 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102306789/10000000000 : ℝ)^543 ≤ (6497745891707/50000000000000 : ℝ)^415 := by
    have hnat : (2102306789 : ℕ)^543*50000000000000^415 ≤ 6497745891707^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102306789 10000000000 6497745891707 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167224963/312500000 : ℝ), (654394379/1250000000 : ℝ), (-2102306789/10000000000 : ℝ)] ![(4412617076597/10000000000000 : ℝ), (21439168719893/50000000000000 : ℝ), (6497745891707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167224963/312500000 : ℝ)|^543 ≤ (4412617076597/10000000000000 : ℝ)^415
        have hw : |(167224963/312500000 : ℝ)|=(167224963/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654394379/1250000000 : ℝ)|^543 ≤ (21439168719893/50000000000000 : ℝ)^415
        have hw : |(654394379/1250000000 : ℝ)|=(654394379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102306789/10000000000 : ℝ)|^543 ≤ (6497745891707/50000000000000 : ℝ)^415
        have hw : |(-2102306789/10000000000 : ℝ)|=(2102306789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1078729861/2500000000 : ℝ)*x 0 + (82404801/200000000 : ℝ)*x 1 + (1129500939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078729861/2500000000 : ℝ)^543 ≤ (4161941479057/12500000000000 : ℝ)^415 := by
    have hnat : (1078729861 : ℕ)^543*12500000000000^415 ≤ 4161941479057^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078729861 2500000000 4161941479057 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82404801/200000000 : ℝ)^543 ≤ (7835949750287/25000000000000 : ℝ)^415 := by
    have hnat : (82404801 : ℕ)^543*25000000000000^415 ≤ 7835949750287^415*200000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82404801 200000000 7835949750287 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129500939/2500000000 : ℝ)^543 ≤ (7072133831317/20000000000000 : ℝ)^415 := by
    have hnat : (1129500939 : ℕ)^543*20000000000000^415 ≤ 7072133831317^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129500939 2500000000 7072133831317 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078729861/2500000000 : ℝ), (82404801/200000000 : ℝ), (1129500939/2500000000 : ℝ)] ![(4161941479057/12500000000000 : ℝ), (7835949750287/25000000000000 : ℝ), (7072133831317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078729861/2500000000 : ℝ)|^543 ≤ (4161941479057/12500000000000 : ℝ)^415
        have hw : |(1078729861/2500000000 : ℝ)|=(1078729861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82404801/200000000 : ℝ)|^543 ≤ (7835949750287/25000000000000 : ℝ)^415
        have hw : |(82404801/200000000 : ℝ)|=(82404801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129500939/2500000000 : ℝ)|^543 ≤ (7072133831317/20000000000000 : ℝ)^415
        have hw : |(1129500939/2500000000 : ℝ)|=(1129500939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1003438369/5000000000 : ℝ)*x 0 + (5235916433/10000000000 : ℝ)*x 1 + (1355333259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003438369/5000000000 : ℝ)^543 ≤ (12229101600619/100000000000000 : ℝ)^415 := by
    have hnat : (1003438369 : ℕ)^543*100000000000000^415 ≤ 12229101600619^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003438369 5000000000 12229101600619 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5235916433/10000000000 : ℝ)^543 ≤ (10721624327761/25000000000000 : ℝ)^415 := by
    have hnat : (5235916433 : ℕ)^543*25000000000000^415 ≤ 10721624327761^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235916433 10000000000 10721624327761 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355333259/2500000000 : ℝ)^543 ≤ (2805275067073/6250000000000 : ℝ)^415 := by
    have hnat : (1355333259 : ℕ)^543*6250000000000^415 ≤ 2805275067073^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355333259 2500000000 2805275067073 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1003438369/5000000000 : ℝ), (5235916433/10000000000 : ℝ), (1355333259/2500000000 : ℝ)] ![(12229101600619/100000000000000 : ℝ), (10721624327761/25000000000000 : ℝ), (2805275067073/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1003438369/5000000000 : ℝ)|^543 ≤ (12229101600619/100000000000000 : ℝ)^415
        have hw : |(-1003438369/5000000000 : ℝ)|=(1003438369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5235916433/10000000000 : ℝ)|^543 ≤ (10721624327761/25000000000000 : ℝ)^415
        have hw : |(5235916433/10000000000 : ℝ)|=(5235916433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355333259/2500000000 : ℝ)|^543 ≤ (2805275067073/6250000000000 : ℝ)^415
        have hw : |(1355333259/2500000000 : ℝ)|=(1355333259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2651410691/5000000000 : ℝ)*x 0 + (-1916128651/10000000000 : ℝ)*x 1 + (169416663/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651410691/5000000000 : ℝ)^543 ≤ (21802468504637/50000000000000 : ℝ)^415 := by
    have hnat : (2651410691 : ℕ)^543*50000000000000^415 ≤ 21802468504637^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651410691 5000000000 21802468504637 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916128651/10000000000 : ℝ)^543 ≤ (5755329973357/50000000000000 : ℝ)^415 := by
    have hnat : (1916128651 : ℕ)^543*50000000000000^415 ≤ 5755329973357^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916128651 10000000000 5755329973357 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169416663/312500000 : ℝ)^543 ≤ (44884403023073/100000000000000 : ℝ)^415 := by
    have hnat : (169416663 : ℕ)^543*100000000000000^415 ≤ 44884403023073^415*312500000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169416663 312500000 44884403023073 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651410691/5000000000 : ℝ), (-1916128651/10000000000 : ℝ), (169416663/312500000 : ℝ)] ![(21802468504637/50000000000000 : ℝ), (5755329973357/50000000000000 : ℝ), (44884403023073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651410691/5000000000 : ℝ)|^543 ≤ (21802468504637/50000000000000 : ℝ)^415
        have hw : |(2651410691/5000000000 : ℝ)|=(2651410691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916128651/10000000000 : ℝ)|^543 ≤ (5755329973357/50000000000000 : ℝ)^415
        have hw : |(-1916128651/10000000000 : ℝ)|=(1916128651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169416663/312500000 : ℝ)|^543 ≤ (44884403023073/100000000000000 : ℝ)^415
        have hw : |(169416663/312500000 : ℝ)|=(169416663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (132570547/250000000 : ℝ)*x 0 + (5421332831/10000000000 : ℝ)*x 1 + (-1916128501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132570547/250000000 : ℝ)^543 ≤ (43604942367361/100000000000000 : ℝ)^415 := by
    have hnat : (132570547 : ℕ)^543*100000000000000^415 ≤ 43604942367361^415*250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132570547 250000000 43604942367361 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421332831/10000000000 : ℝ)^543 ≤ (22442199426221/50000000000000 : ℝ)^415 := by
    have hnat : (5421332831 : ℕ)^543*50000000000000^415 ≤ 22442199426221^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421332831 10000000000 22442199426221 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916128501/10000000000 : ℝ)^543 ≤ (11510658767701/100000000000000 : ℝ)^415 := by
    have hnat : (1916128501 : ℕ)^543*100000000000000^415 ≤ 11510658767701^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916128501 10000000000 11510658767701 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132570547/250000000 : ℝ), (5421332831/10000000000 : ℝ), (-1916128501/10000000000 : ℝ)] ![(43604942367361/100000000000000 : ℝ), (22442199426221/50000000000000 : ℝ), (11510658767701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132570547/250000000 : ℝ)|^543 ≤ (43604942367361/100000000000000 : ℝ)^415
        have hw : |(132570547/250000000 : ℝ)|=(132570547/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421332831/10000000000 : ℝ)|^543 ≤ (22442199426221/50000000000000 : ℝ)^415
        have hw : |(5421332831/10000000000 : ℝ)|=(5421332831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916128501/10000000000 : ℝ)|^543 ≤ (11510658767701/100000000000000 : ℝ)^415
        have hw : |(-1916128501/10000000000 : ℝ)|=(1916128501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s3_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (86299127/200000000 : ℝ)*x 0 + (4516383547/10000000000 : ℝ)*x 1 + (4121869347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86299127/200000000 : ℝ)^543 ≤ (6659180889871/20000000000000 : ℝ)^415 := by
    have hnat : (86299127 : ℕ)^543*20000000000000^415 ≤ 6659180889871^415*200000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86299127 200000000 6659180889871 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516383547/10000000000 : ℝ)^543 ≤ (35344078153673/100000000000000 : ℝ)^415 := by
    have hnat : (4516383547 : ℕ)^543*100000000000000^415 ≤ 35344078153673^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516383547 10000000000 35344078153673 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4121869347/10000000000 : ℝ)^543 ≤ (31360017385431/100000000000000 : ℝ)^415 := by
    have hnat : (4121869347 : ℕ)^543*100000000000000^415 ≤ 31360017385431^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121869347 10000000000 31360017385431 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86299127/200000000 : ℝ), (4516383547/10000000000 : ℝ), (4121869347/10000000000 : ℝ)] ![(6659180889871/20000000000000 : ℝ), (35344078153673/100000000000000 : ℝ), (31360017385431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86299127/200000000 : ℝ)|^543 ≤ (6659180889871/20000000000000 : ℝ)^415
        have hw : |(86299127/200000000 : ℝ)|=(86299127/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516383547/10000000000 : ℝ)|^543 ≤ (35344078153673/100000000000000 : ℝ)^415
        have hw : |(4516383547/10000000000 : ℝ)|=(4516383547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4121869347/10000000000 : ℝ)|^543 ≤ (31360017385431/100000000000000 : ℝ)^415
        have hw : |(4121869347/10000000000 : ℝ)|=(4121869347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11017/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7487/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5057/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5057/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5057/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5057/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5057/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5057/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5057/50000 : ℝ) ^ (4343/1024 : ℝ) ≤ (1505248966081959/25000000000000000000 : ℝ) := by
    have hpowers : (5057/50000 : ℝ)^4343 ≤ (1505248966081959/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5057 : ℕ)^4343*25000000000000000000^1024 ≤ 1505248966081959^1024*50000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5057 50000 1505248966081959 25000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5057/50000 : ℝ)) (X := (1505248966081959/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15947/100000 : ℝ) ^ (4343/1024 : ℝ) ≤ (20766506098539929/50000000000000000000 : ℝ) := by
    have hpowers : (15947/100000 : ℝ)^4343 ≤ (20766506098539929/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15947 : ℕ)^4343*50000000000000000000^1024 ≤ 20766506098539929^1024*100000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15947 100000 20766506098539929 50000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15947/100000 : ℝ)) (X := (20766506098539929/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501505248966081959/12500000000000000000 : ℝ) ≤ (5000141957542911/5000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (12501505248966081959/12500000000000000000 : ℝ)^1024 ≤ (5000141957542911/5000000000000000 : ℝ)^4343 := by
      have hnat : (12501505248966081959 : ℕ)^1024*5000000000000000^4343 ≤ 5000141957542911^4343*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501505248966081959 12500000000000000000 5000141957542911 5000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141957542911/5000000000000000 : ℝ)) (X := (12501505248966081959/12500000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023777004030703847/50000000000000000000 : ℝ) ≤ (10001121032889521/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50023777004030703847/50000000000000000000 : ℝ)^1024 ≤ (10001121032889521/10000000000000000 : ℝ)^4343 := by
      have hnat : (50023777004030703847 : ℕ)^1024*10000000000000000^4343 ≤ 10001121032889521^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023777004030703847 50000000000000000000 10001121032889521 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001121032889521/10000000000000000 : ℝ)) (X := (50023777004030703847/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020766506098539929/25000000000000000000 : ℝ) ≤ (500097907534661/500000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (25020766506098539929/25000000000000000000 : ℝ)^1024 ≤ (500097907534661/500000000000000 : ℝ)^4343 := by
      have hnat : (25020766506098539929 : ℕ)^1024*500000000000000^4343 ≤ 500097907534661^4343*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020766506098539929 25000000000000000000 500097907534661 500000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500097907534661/500000000000000 : ℝ)) (X := (25020766506098539929/25000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1505248966081959/25000000000000000000 : ℝ) ≤ ((29157361428881188177/29165000000000000000 : ℝ)+2*(837117803699/583300000000000 : ℝ)*(5057/50000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (29157361428881188177/29165000000000000000 : ℝ)+2*(837117803699/583300000000000 : ℝ)*(5057/50000 : ℝ)=(5000141957542911/5000000000000000 : ℝ) by norm_num, show 1+2*(1505248966081959/25000000000000000000 : ℝ)=(12501505248966081959/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20766506098539929/50000000000000000000 : ℝ)+(1505248966081959/25000000000000000000 : ℝ) ≤ ((29157361428881188177/29165000000000000000 : ℝ)+(837117803699/583300000000000 : ℝ)*((15947/100000 : ℝ)+(5057/50000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (29157361428881188177/29165000000000000000 : ℝ)+(837117803699/583300000000000 : ℝ)*((15947/100000 : ℝ)+(5057/50000 : ℝ))=(10001121032889521/10000000000000000 : ℝ) by norm_num, show 1+(20766506098539929/50000000000000000000 : ℝ)+(1505248966081959/25000000000000000000 : ℝ)=(50023777004030703847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20766506098539929/50000000000000000000 : ℝ) ≤ ((29157361428881188177/29165000000000000000 : ℝ)+2*(837117803699/583300000000000 : ℝ)*(15947/100000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (29157361428881188177/29165000000000000000 : ℝ)+2*(837117803699/583300000000000 : ℝ)*(15947/100000 : ℝ)=(500097907534661/500000000000000 : ℝ) by norm_num, show 1+2*(20766506098539929/50000000000000000000 : ℝ)=(25020766506098539929/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29157361428881188177/29165000000000000000 : ℝ)*(X 1 0+X 2 0)+(837117803699/583300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (5057/50000 : ℝ)) (hi := (15947/100000 : ℝ)) (c := (29157361428881188177/29165000000000000000 : ℝ)) (alpha := (837117803699/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29157361428881188177/29165000000000000000 : ℝ)*(X 0 1+X 2 1)+(837117803699/583300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (5057/50000 : ℝ)) (hi := (15947/100000 : ℝ)) (c := (29157361428881188177/29165000000000000000 : ℝ)) (alpha := (837117803699/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29157361428881188177/29165000000000000000 : ℝ)*(X 0 2+X 1 2)+(837117803699/583300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (5057/50000 : ℝ)) (hi := (15947/100000 : ℝ)) (c := (29157361428881188177/29165000000000000000 : ℝ)) (alpha := (837117803699/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-501714827/2500000000 : ℝ)*X 0 0+(5422099523/10000000000 : ℝ)*X 0 1+(327197163/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535119881/1000000000 : ℝ)*X 1 0+(-131394179/625000000 : ℝ)*X 1 1+(5235154981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167224963/312500000 : ℝ)*X 2 0+(654394379/1250000000 : ℝ)*X 2 1+(-2102306789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078729861/2500000000 : ℝ)*X 0 0+(82404801/200000000 : ℝ)*X 0 1+(1129500939/2500000000 : ℝ)*X 0 2+(1078729861/2500000000 : ℝ)*X 1 0+(82404801/200000000 : ℝ)*X 1 1+(1129500939/2500000000 : ℝ)*X 1 2+(1078729861/2500000000 : ℝ)*X 2 0+(82404801/200000000 : ℝ)*X 2 1+(1129500939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1003438369/5000000000 : ℝ)*X 0 0+(5235916433/10000000000 : ℝ)*X 0 1+(1355333259/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651410691/5000000000 : ℝ)*X 1 0+(-1916128651/10000000000 : ℝ)*X 1 1+(169416663/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132570547/250000000 : ℝ)*X 2 0+(5421332831/10000000000 : ℝ)*X 2 1+(-1916128501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((86299127/200000000 : ℝ)*X 0 0+(4516383547/10000000000 : ℝ)*X 0 1+(4121869347/10000000000 : ℝ)*X 0 2+(86299127/200000000 : ℝ)*X 1 0+(4516383547/10000000000 : ℝ)*X 1 1+(4121869347/10000000000 : ℝ)*X 1 2+(86299127/200000000 : ℝ)*X 2 0+(4516383547/10000000000 : ℝ)*X 2 1+(4121869347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2495186092587509046379929873/364562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (933634563/100000000000000 : ℝ)*(base19) + (297067203/50000000000000 : ℝ)*(base23) + (184882817/100000000000000 : ℝ)*(lower2) + (192571893/100000000000000 : ℝ)*(upper3) + (17633813/100000000000000 : ℝ)*(upper5) + (982910473979883/25000000000000 : ℝ)*(major0) + (982910473979883/25000000000000 : ℝ)*(major1) + (982910473979883/25000000000000 : ℝ)*(major2) + (5349195532820317/100000000000000 : ℝ)*(sp0) + (5349218867110329/100000000000000 : ℝ)*(sp1) + (2674609603305243/50000000000000 : ℝ)*(sp2) + (628514439903621/25000000000000 : ℝ)*(sp3) + (12133962287/50000000000000 : ℝ)*(sp4) + (6003335343/100000000000000 : ℝ)*(sp7) + (2514063762949827/100000000000000 : ℝ)*(f.failure) + (5349219800744891/100000000000000 : ℝ)*(f.sum) + (30981129884151/14582500000000000000000000000 : ℝ)*base66 + (4354055609236043291/729125000000000000000000000000000 : ℝ)*base67 + (4157320310819331709/729125000000000000000000000000000 : ℝ)*base70 + (9136575534127206709/729125000000000000000000000000000 : ℝ)*base72 + (36239128115643/29165000000000000000000000000 : ℝ)*base73 + (11433915881908956709/729125000000000000000000000000000 : ℝ)*base76 + (4444926189668043291/729125000000000000000000000000000 : ℝ)*base77 + (10217749744942331709/729125000000000000000000000000000 : ℝ)*base80 + (86760056882847/29165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6532599/5000000000000000000000 : ℝ)*base90 + (6532599/5000000000000000000000 : ℝ)*base92 + (6532599/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4455256341955828866854496249/1458250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (708966689/100000000000000 : ℝ)*(base19) + (151942467/10000000000000 : ℝ)*(base23) + (134841533/100000000000000 : ℝ)*(upper3) + (115041461/100000000000000 : ℝ)*(lower4) + (86939923/50000000000000 : ℝ)*(upper5) + (3964013376219379/100000000000000 : ℝ)*(major0) + (3964013376219379/100000000000000 : ℝ)*(major1) + (3964013376219379/100000000000000 : ℝ)*(major2) + (1540724809/10000000000000 : ℝ)*(sp1) + (24946144727/100000000000000 : ℝ)*(sp2) + (5393263147507193/100000000000000 : ℝ)*(sp4) + (1078649406258483/20000000000000 : ℝ)*(sp5) + (1348309170484449/25000000000000 : ℝ)*(sp6) + (2534763503091307/100000000000000 : ℝ)*(sp7) + (2534763503091307/100000000000000 : ℝ)*(f.failure) + (5393263147507193/100000000000000 : ℝ)*(f.sum) + (19753102171281/29165000000000000000000000000 : ℝ)*base65 + (3003567351462132083/2916500000000000000000000000000000 : ℝ)*base67 + (35057825026291367917/2916500000000000000000000000000000 : ℝ)*base70 + (29065716544140867917/2916500000000000000000000000000000 : ℝ)*base72 + (129848615156261/29165000000000000000000000000 : ℝ)*base73 + (82468638546294367917/2916500000000000000000000000000000 : ℝ)*base76 + (18495239345093867917/2916500000000000000000000000000000 : ℝ)*base78 + (3311275101740632083/2916500000000000000000000000000000 : ℝ)*base79 + (121464356123529/29165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3872641/5000000000000000000000 : ℝ)*base89 + (3872641/5000000000000000000000 : ℝ)*base91 + (3872641/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1384_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7487/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1384_s4_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004008839/5000000000 : ℝ)*x 0 + (270621801/500000000 : ℝ)*x 1 + (104881127/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004008839/5000000000 : ℝ)^543 ≤ (191221862387/1562500000000 : ℝ)^415 := by
    have hnat : (1004008839 : ℕ)^543*1562500000000^415 ≤ 191221862387^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004008839 5000000000 191221862387 1562500000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270621801/500000000 : ℝ)^543 ≤ (358304366409/800000000000 : ℝ)^415 := by
    have hnat : (270621801 : ℕ)^543*800000000000^415 ≤ 358304366409^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270621801 500000000 358304366409 800000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104881127/200000000 : ℝ)^543 ≤ (42973754989233/100000000000000 : ℝ)^415 := by
    have hnat : (104881127 : ℕ)^543*100000000000000^415 ≤ 42973754989233^415*200000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104881127 200000000 42973754989233 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004008839/5000000000 : ℝ), (270621801/500000000 : ℝ), (104881127/200000000 : ℝ)] ![(191221862387/1562500000000 : ℝ), (358304366409/800000000000 : ℝ), (42973754989233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004008839/5000000000 : ℝ)|^543 ≤ (191221862387/1562500000000 : ℝ)^415
        have hw : |(-1004008839/5000000000 : ℝ)|=(1004008839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270621801/500000000 : ℝ)|^543 ≤ (358304366409/800000000000 : ℝ)^415
        have hw : |(270621801/500000000 : ℝ)|=(270621801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104881127/200000000 : ℝ)|^543 ≤ (42973754989233/100000000000000 : ℝ)^415
        have hw : |(104881127/200000000 : ℝ)|=(104881127/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348720317/10000000000 : ℝ)*x 0 + (-65431569/312500000 : ℝ)*x 1 + (524405641/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348720317/10000000000 : ℝ)^543 ≤ (2756214449013/6250000000000 : ℝ)^415 := by
    have hnat : (5348720317 : ℕ)^543*6250000000000^415 ≤ 2756214449013^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348720317 10000000000 2756214449013 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65431569/312500000 : ℝ)^543 ≤ (2585362633353/20000000000000 : ℝ)^415 := by
    have hnat : (65431569 : ℕ)^543*20000000000000^415 ≤ 2585362633353^415*312500000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65431569 312500000 2585362633353 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524405641/1000000000 : ℝ)^543 ≤ (4297375563257/10000000000000 : ℝ)^415 := by
    have hnat : (524405641 : ℕ)^543*10000000000000^415 ≤ 4297375563257^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524405641 1000000000 4297375563257 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348720317/10000000000 : ℝ), (-65431569/312500000 : ℝ), (524405641/1000000000 : ℝ)] ![(2756214449013/6250000000000 : ℝ), (2585362633353/20000000000000 : ℝ), (4297375563257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348720317/10000000000 : ℝ)|^543 ≤ (2756214449013/6250000000000 : ℝ)^415
        have hw : |(5348720317/10000000000 : ℝ)|=(5348720317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65431569/312500000 : ℝ)|^543 ≤ (2585362633353/20000000000000 : ℝ)^415
        have hw : |(-65431569/312500000 : ℝ)|=(65431569/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524405641/1000000000 : ℝ)|^543 ≤ (4297375563257/10000000000000 : ℝ)^415
        have hw : |(524405641/1000000000 : ℝ)|=(524405641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674360193/5000000000 : ℝ)*x 0 + (1311014083/2500000000 : ℝ)*x 1 + (-104690511/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674360193/5000000000 : ℝ)^543 ≤ (4409943192857/10000000000000 : ℝ)^415 := by
    have hnat : (2674360193 : ℕ)^543*10000000000000^415 ≤ 4409943192857^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674360193 5000000000 4409943192857 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311014083/2500000000 : ℝ)^543 ≤ (5371719349529/12500000000000 : ℝ)^415 := by
    have hnat : (1311014083 : ℕ)^543*12500000000000^415 ≤ 5371719349529^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311014083 2500000000 5371719349529 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104690511/500000000 : ℝ)^543 ≤ (6463406631851/50000000000000 : ℝ)^415 := by
    have hnat : (104690511 : ℕ)^543*50000000000000^415 ≤ 6463406631851^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104690511 500000000 6463406631851 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674360193/5000000000 : ℝ), (1311014083/2500000000 : ℝ), (-104690511/500000000 : ℝ)] ![(4409943192857/10000000000000 : ℝ), (5371719349529/12500000000000 : ℝ), (6463406631851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674360193/5000000000 : ℝ)|^543 ≤ (4409943192857/10000000000000 : ℝ)^415
        have hw : |(2674360193/5000000000 : ℝ)|=(2674360193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311014083/2500000000 : ℝ)|^543 ≤ (5371719349529/12500000000000 : ℝ)^415
        have hw : |(1311014083/2500000000 : ℝ)|=(1311014083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104690511/500000000 : ℝ)|^543 ≤ (6463406631851/50000000000000 : ℝ)^415
        have hw : |(-104690511/500000000 : ℝ)|=(104690511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4315625597/10000000000 : ℝ)*x 0 + (129371977/312500000 : ℝ)*x 1 + (2249083939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315625597/10000000000 : ℝ)^543 ≤ (33302661590071/100000000000000 : ℝ)^415 := by
    have hnat : (4315625597 : ℕ)^543*100000000000000^415 ≤ 33302661590071^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315625597 10000000000 33302661590071 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129371977/312500000 : ℝ)^543 ≤ (15769831477057/50000000000000 : ℝ)^415 := by
    have hnat : (129371977 : ℕ)^543*50000000000000^415 ≤ 15769831477057^415*312500000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129371977 312500000 15769831477057 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249083939/5000000000 : ℝ)^543 ≤ (35157675437323/100000000000000 : ℝ)^415 := by
    have hnat : (2249083939 : ℕ)^543*100000000000000^415 ≤ 35157675437323^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249083939 5000000000 35157675437323 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315625597/10000000000 : ℝ), (129371977/312500000 : ℝ), (2249083939/5000000000 : ℝ)] ![(33302661590071/100000000000000 : ℝ), (15769831477057/50000000000000 : ℝ), (35157675437323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315625597/10000000000 : ℝ)|^543 ≤ (33302661590071/100000000000000 : ℝ)^415
        have hw : |(4315625597/10000000000 : ℝ)|=(4315625597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129371977/312500000 : ℝ)|^543 ≤ (15769831477057/50000000000000 : ℝ)^415
        have hw : |(129371977/312500000 : ℝ)|=(129371977/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249083939/5000000000 : ℝ)|^543 ≤ (35157675437323/100000000000000 : ℝ)^415
        have hw : |(2249083939/5000000000 : ℝ)|=(2249083939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008030213/10000000000 : ℝ)*x 0 + (1311168649/2500000000 : ℝ)*x 1 + (1352953629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008030213/10000000000 : ℝ)^543 ≤ (611914957641/5000000000000 : ℝ)^415 := by
    have hnat : (2008030213 : ℕ)^543*5000000000000^415 ≤ 611914957641^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008030213 10000000000 611914957641 5000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311168649/2500000000 : ℝ)^543 ≤ (21490192062377/50000000000000 : ℝ)^415 := by
    have hnat : (1311168649 : ℕ)^543*50000000000000^415 ≤ 21490192062377^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311168649 2500000000 21490192062377 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352953629/2500000000 : ℝ)^543 ≤ (22390658348039/50000000000000 : ℝ)^415 := by
    have hnat : (1352953629 : ℕ)^543*50000000000000^415 ≤ 22390658348039^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352953629 2500000000 22390658348039 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008030213/10000000000 : ℝ), (1311168649/2500000000 : ℝ), (1352953629/2500000000 : ℝ)] ![(611914957641/5000000000000 : ℝ), (21490192062377/50000000000000 : ℝ), (22390658348039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008030213/10000000000 : ℝ)|^543 ≤ (611914957641/5000000000000 : ℝ)^415
        have hw : |(-2008030213/10000000000 : ℝ)|=(2008030213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311168649/2500000000 : ℝ)|^543 ≤ (21490192062377/50000000000000 : ℝ)^415
        have hw : |(1311168649/2500000000 : ℝ)|=(1311168649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352953629/2500000000 : ℝ)|^543 ≤ (22390658348039/50000000000000 : ℝ)^415
        have hw : |(1352953629/2500000000 : ℝ)|=(1352953629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305147147/10000000000 : ℝ)*x 0 + (-1926051961/10000000000 : ℝ)*x 1 + (1352953651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305147147/10000000000 : ℝ)^543 ≤ (43629962096449/100000000000000 : ℝ)^415 := by
    have hnat : (5305147147 : ℕ)^543*100000000000000^415 ≤ 43629962096449^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305147147 10000000000 43629962096449 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926051961/10000000000 : ℝ)^543 ≤ (5794360117843/50000000000000 : ℝ)^415 := by
    have hnat : (1926051961 : ℕ)^543*50000000000000^415 ≤ 5794360117843^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926051961 10000000000 5794360117843 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352953651/2500000000 : ℝ)^543 ≤ (44781317648849/100000000000000 : ℝ)^415 := by
    have hnat : (1352953651 : ℕ)^543*100000000000000^415 ≤ 44781317648849^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352953651 2500000000 44781317648849 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305147147/10000000000 : ℝ), (-1926051961/10000000000 : ℝ), (1352953651/2500000000 : ℝ)] ![(43629962096449/100000000000000 : ℝ), (5794360117843/50000000000000 : ℝ), (44781317648849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305147147/10000000000 : ℝ)|^543 ≤ (43629962096449/100000000000000 : ℝ)^415
        have hw : |(5305147147/10000000000 : ℝ)|=(5305147147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1926051961/10000000000 : ℝ)|^543 ≤ (5794360117843/50000000000000 : ℝ)^415
        have hw : |(-1926051961/10000000000 : ℝ)|=(1926051961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352953651/2500000000 : ℝ)|^543 ≤ (44781317648849/100000000000000 : ℝ)^415
        have hw : |(1352953651/2500000000 : ℝ)|=(1352953651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652573511/5000000000 : ℝ)*x 0 + (1352953673/2500000000 : ℝ)*x 1 + (-481513003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652573511/5000000000 : ℝ)^543 ≤ (21814980375683/50000000000000 : ℝ)^415 := by
    have hnat : (2652573511 : ℕ)^543*50000000000000^415 ≤ 21814980375683^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652573511 5000000000 21814980375683 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352953673/2500000000 : ℝ)^543 ≤ (2239065930081/5000000000000 : ℝ)^415 := by
    have hnat : (1352953673 : ℕ)^543*5000000000000^415 ≤ 2239065930081^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352953673 2500000000 2239065930081 5000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481513003/2500000000 : ℝ)^543 ≤ (1158872063719/10000000000000 : ℝ)^415 := by
    have hnat : (481513003 : ℕ)^543*10000000000000^415 ≤ 1158872063719^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481513003 2500000000 1158872063719 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652573511/5000000000 : ℝ), (1352953673/2500000000 : ℝ), (-481513003/2500000000 : ℝ)] ![(21814980375683/50000000000000 : ℝ), (2239065930081/5000000000000 : ℝ), (1158872063719/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652573511/5000000000 : ℝ)|^543 ≤ (21814980375683/50000000000000 : ℝ)^415
        have hw : |(2652573511/5000000000 : ℝ)|=(2652573511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352953673/2500000000 : ℝ)|^543 ≤ (2239065930081/5000000000000 : ℝ)^415
        have hw : |(1352953673/2500000000 : ℝ)|=(1352953673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-481513003/2500000000 : ℝ)|^543 ≤ (1158872063719/10000000000000 : ℝ)^415
        have hw : |(-481513003/2500000000 : ℝ)|=(481513003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s4_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (863130449/2000000000 : ℝ)*x 0 + (1798741/4000000 : ℝ)*x 1 + (129413301/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863130449/2000000000 : ℝ)^543 ≤ (33302930651813/100000000000000 : ℝ)^415 := by
    have hnat : (863130449 : ℕ)^543*100000000000000^415 ≤ 33302930651813^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863130449 2000000000 33302930651813 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798741/4000000 : ℝ)^543 ≤ (439302800573/1250000000000 : ℝ)^415 := by
    have hnat : (1798741 : ℕ)^543*1250000000000^415 ≤ 439302800573^415*4000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798741 4000000 439302800573 1250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129413301/312500000 : ℝ)^543 ≤ (31552845288081/100000000000000 : ℝ)^415 := by
    have hnat : (129413301 : ℕ)^543*100000000000000^415 ≤ 31552845288081^415*312500000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129413301 312500000 31552845288081 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863130449/2000000000 : ℝ), (1798741/4000000 : ℝ), (129413301/312500000 : ℝ)] ![(33302930651813/100000000000000 : ℝ), (439302800573/1250000000000 : ℝ), (31552845288081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863130449/2000000000 : ℝ)|^543 ≤ (33302930651813/100000000000000 : ℝ)^415
        have hw : |(863130449/2000000000 : ℝ)|=(863130449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1798741/4000000 : ℝ)|^543 ≤ (439302800573/1250000000000 : ℝ)^415
        have hw : |(1798741/4000000 : ℝ)|=(1798741/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129413301/312500000 : ℝ)|^543 ≤ (31552845288081/100000000000000 : ℝ)^415
        have hw : |(129413301/312500000 : ℝ)|=(129413301/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7487/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7487/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7487/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7487/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7487/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7487/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7487/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11017/100000 : ℝ) ^ (4343/1024 : ℝ) ≤ (270419883813849/3125000000000000000 : ℝ) := by
    have hpowers : (11017/100000 : ℝ)^4343 ≤ (270419883813849/3125000000000000000 : ℝ)^1024 := by
      have hnat : (11017 : ℕ)^4343*3125000000000000000^1024 ≤ 270419883813849^1024*100000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11017 100000 270419883813849 3125000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11017/100000 : ℝ)) (X := (270419883813849/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7487/50000 : ℝ) ^ (4343/1024 : ℝ) ≤ (3975060955627057/12500000000000000000 : ℝ) := by
    have hpowers : (7487/50000 : ℝ)^4343 ≤ (3975060955627057/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7487 : ℕ)^4343*12500000000000000000^1024 ≤ 3975060955627057^1024*50000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7487 50000 3975060955627057 12500000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7487/50000 : ℝ)) (X := (3975060955627057/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562770419883813849/1562500000000000000 : ℝ) ≤ (1000040803743111/1000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (1562770419883813849/1562500000000000000 : ℝ)^1024 ≤ (1000040803743111/1000000000000000 : ℝ)^4343 := by
      have hnat : (1562770419883813849 : ℕ)^1024*1000000000000000^4343 ≤ 1000040803743111^4343*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562770419883813849 1562500000000000000 1000040803743111 1000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000040803743111/1000000000000000 : ℝ)) (X := (1562770419883813849/1562500000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505056740490882453/12500000000000000000 : ℝ) ≤ (2000190736432203/2000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (12505056740490882453/12500000000000000000 : ℝ)^1024 ≤ (2000190736432203/2000000000000000 : ℝ)^4343 := by
      have hnat : (12505056740490882453 : ℕ)^1024*2000000000000000^4343 ≤ 2000190736432203^4343*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505056740490882453 12500000000000000000 2000190736432203 2000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000190736432203/2000000000000000 : ℝ)) (X := (12505056740490882453/12500000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253975060955627057/6250000000000000000 : ℝ) ≤ (250037483172273/250000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (6253975060955627057/6250000000000000000 : ℝ)^1024 ≤ (250037483172273/250000000000000 : ℝ)^4343 := by
      have hnat : (6253975060955627057 : ℕ)^1024*250000000000000^4343 ≤ 250037483172273^4343*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253975060955627057 6250000000000000000 250037483172273 250000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250037483172273/250000000000000 : ℝ)) (X := (6253975060955627057/6250000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(270419883813849/3125000000000000000 : ℝ) ≤ ((26373061245424117/26380000000000000 : ℝ)+2*(36376315327/26380000000000 : ℝ)*(11017/100000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (26373061245424117/26380000000000000 : ℝ)+2*(36376315327/26380000000000 : ℝ)*(11017/100000 : ℝ)=(1000040803743111/1000000000000000 : ℝ) by norm_num, show 1+2*(270419883813849/3125000000000000000 : ℝ)=(1562770419883813849/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3975060955627057/12500000000000000000 : ℝ)+(270419883813849/3125000000000000000 : ℝ) ≤ ((26373061245424117/26380000000000000 : ℝ)+(36376315327/26380000000000 : ℝ)*((7487/50000 : ℝ)+(11017/100000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (26373061245424117/26380000000000000 : ℝ)+(36376315327/26380000000000 : ℝ)*((7487/50000 : ℝ)+(11017/100000 : ℝ))=(2000190736432203/2000000000000000 : ℝ) by norm_num, show 1+(3975060955627057/12500000000000000000 : ℝ)+(270419883813849/3125000000000000000 : ℝ)=(12505056740490882453/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3975060955627057/12500000000000000000 : ℝ) ≤ ((26373061245424117/26380000000000000 : ℝ)+2*(36376315327/26380000000000 : ℝ)*(7487/50000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (26373061245424117/26380000000000000 : ℝ)+2*(36376315327/26380000000000 : ℝ)*(7487/50000 : ℝ)=(250037483172273/250000000000000 : ℝ) by norm_num, show 1+2*(3975060955627057/12500000000000000000 : ℝ)=(6253975060955627057/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26373061245424117/26380000000000000 : ℝ)*(X 1 0+X 2 0)+(36376315327/26380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (7487/50000 : ℝ)) (c := (26373061245424117/26380000000000000 : ℝ)) (alpha := (36376315327/26380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26373061245424117/26380000000000000 : ℝ)*(X 0 1+X 2 1)+(36376315327/26380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (7487/50000 : ℝ)) (c := (26373061245424117/26380000000000000 : ℝ)) (alpha := (36376315327/26380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26373061245424117/26380000000000000 : ℝ)*(X 0 2+X 1 2)+(36376315327/26380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (7487/50000 : ℝ)) (c := (26373061245424117/26380000000000000 : ℝ)) (alpha := (36376315327/26380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1004008839/5000000000 : ℝ)*X 0 0+(270621801/500000000 : ℝ)*X 0 1+(104881127/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348720317/10000000000 : ℝ)*X 1 0+(-65431569/312500000 : ℝ)*X 1 1+(524405641/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674360193/5000000000 : ℝ)*X 2 0+(1311014083/2500000000 : ℝ)*X 2 1+(-104690511/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315625597/10000000000 : ℝ)*X 0 0+(129371977/312500000 : ℝ)*X 0 1+(2249083939/5000000000 : ℝ)*X 0 2+(4315625597/10000000000 : ℝ)*X 1 0+(129371977/312500000 : ℝ)*X 1 1+(2249083939/5000000000 : ℝ)*X 1 2+(4315625597/10000000000 : ℝ)*X 2 0+(129371977/312500000 : ℝ)*X 2 1+(2249083939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2008030213/10000000000 : ℝ)*X 0 0+(1311168649/2500000000 : ℝ)*X 0 1+(1352953629/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305147147/10000000000 : ℝ)*X 1 0+(-1926051961/10000000000 : ℝ)*X 1 1+(1352953651/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652573511/5000000000 : ℝ)*X 2 0+(1352953673/2500000000 : ℝ)*X 2 1+(-481513003/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863130449/2000000000 : ℝ)*X 0 0+(1798741/4000000 : ℝ)*X 0 1+(129413301/312500000 : ℝ)*X 0 2+(863130449/2000000000 : ℝ)*X 1 0+(1798741/4000000 : ℝ)*X 1 1+(129413301/312500000 : ℝ)*X 1 2+(863130449/2000000000 : ℝ)*X 2 0+(1798741/4000000 : ℝ)*X 2 1+(129413301/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1038331429276301712088131/164875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216741431/100000000000000 : ℝ)*(base19) + (245228509/20000000000000 : ℝ)*(base23) + (17975383/50000000000000 : ℝ)*(lower2) + (193253717/100000000000000 : ℝ)*(upper3) + (142621147/100000000000000 : ℝ)*(upper5) + (136410427710461/3125000000000 : ℝ)*(major0) + (136410427710461/3125000000000 : ℝ)*(major1) + (136410427710461/3125000000000 : ℝ)*(major2) + (185593271673233/3125000000000 : ℝ)*(sp0) + (742376071971391/12500000000000 : ℝ)*(sp1) + (2969504283185007/50000000000000 : ℝ)*(sp2) + (697811121207979/25000000000000 : ℝ)*(sp3) + (25098969103/100000000000000 : ℝ)*(sp4) + (3221550517/25000000000000 : ℝ)*(sp7) + (21806698211203/781250000000 : ℝ)*(f.failure) + (5939009792512559/100000000000000 : ℝ)*(f.sum) + (1187025158291/1319000000000000000000000000 : ℝ)*base66 + (225254499284313/82437500000000000000000000000 : ℝ)*base68 + (227788231018187/82437500000000000000000000000 : ℝ)*base69 + (29001896330437/82437500000000000000000000000 : ℝ)*base71 + (84031845681/82437500000000000000000000 : ℝ)*base74 + (80003700986437/82437500000000000000000000000 : ℝ)*base75 + (104983593365313/82437500000000000000000000000 : ℝ)*base78 + (501107577674437/82437500000000000000000000000 : ℝ)*base79 + (1346389813/20609375000000000000000000 : ℝ)*base82 + (135511/39062500000000000000 : ℝ)*base90 + (135511/39062500000000000000 : ℝ)*base92 + (135511/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5556158949635521522853307/1319000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (758226663/100000000000000 : ℝ)*(base19) + (641317077/100000000000000 : ℝ)*(base23) + (3421189/2500000000000 : ℝ)*(upper3) + (7745301/50000000000000 : ℝ)*(lower4) + (11998631/12500000000000 : ℝ)*(upper5) + (4397472110425643/100000000000000 : ℝ)*(major0) + (4397472110425643/100000000000000 : ℝ)*(major1) + (4397472110425643/100000000000000 : ℝ)*(major2) + (3143707693/20000000000000 : ℝ)*(sp1) + (1509302557/10000000000000 : ℝ)*(sp2) + (5983008107103761/100000000000000 : ℝ)*(sp4) + (5982991630338633/100000000000000 : ℝ)*(sp5) + (2991496186380557/50000000000000 : ℝ)*(sp6) + (1405967986667049/50000000000000 : ℝ)*(sp7) + (1405967986667049/50000000000000 : ℝ)*(f.failure) + (5983008107103761/100000000000000 : ℝ)*(f.sum) + (2518874289369/659500000000000000000000000 : ℝ)*base65 + (6406605209034769/2638000000000000000000000000000 : ℝ)*base68 + (21693122671237231/2638000000000000000000000000000 : ℝ)*base69 + (8856708145614769/2638000000000000000000000000000 : ℝ)*base72 + (1348348939697/329750000000000000000000000 : ℝ)*base73 + (47409369408009231/2638000000000000000000000000000 : ℝ)*base75 + (12939901202449231/2638000000000000000000000000000 : ℝ)*base77 + (8642813962029231/2638000000000000000000000000000 : ℝ)*base79 + (4800336161669/1319000000000000000000000000 : ℝ)*base81 + (19223813/2500000000000000000000 : ℝ)*base90 + (19223813/2500000000000000000000 : ℝ)*base92 + (19223813/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1384_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7487/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1384_s5_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-502051071/2500000000 : ℝ)*x 0 + (5410806281/10000000000 : ℝ)*x 1 + (1311390781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502051071/2500000000 : ℝ)^543 ≤ (6119843648833/50000000000000 : ℝ)^415 := by
    have hnat : (502051071 : ℕ)^543*50000000000000^415 ≤ 6119843648833^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502051071 2500000000 6119843648833 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410806281/10000000000 : ℝ)^543 ≤ (22385200455457/50000000000000 : ℝ)^415 := by
    have hnat : (5410806281 : ℕ)^543*50000000000000^415 ≤ 22385200455457^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410806281 10000000000 22385200455457 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311390781/2500000000 : ℝ)^543 ≤ (42989911777981/100000000000000 : ℝ)^415 := by
    have hnat : (1311390781 : ℕ)^543*100000000000000^415 ≤ 42989911777981^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311390781 2500000000 42989911777981 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502051071/2500000000 : ℝ), (5410806281/10000000000 : ℝ), (1311390781/2500000000 : ℝ)] ![(6119843648833/50000000000000 : ℝ), (22385200455457/50000000000000 : ℝ), (42989911777981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502051071/2500000000 : ℝ)|^543 ≤ (6119843648833/50000000000000 : ℝ)^415
        have hw : |(-502051071/2500000000 : ℝ)|=(502051071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410806281/10000000000 : ℝ)|^543 ≤ (22385200455457/50000000000000 : ℝ)^415
        have hw : |(5410806281/10000000000 : ℝ)|=(5410806281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311390781/2500000000 : ℝ)|^543 ≤ (42989911777981/100000000000000 : ℝ)^415
        have hw : |(1311390781/2500000000 : ℝ)|=(1311390781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348301379/10000000000 : ℝ)*x 0 + (-2092369487/10000000000 : ℝ)*x 1 + (5245563143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348301379/10000000000 : ℝ)^543 ≤ (44094911799203/100000000000000 : ℝ)^415 := by
    have hnat : (5348301379 : ℕ)^543*100000000000000^415 ≤ 44094911799203^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348301379 10000000000 44094911799203 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092369487/10000000000 : ℝ)^543 ≤ (1614397025369/12500000000000 : ℝ)^415 := by
    have hnat : (2092369487 : ℕ)^543*12500000000000^415 ≤ 1614397025369^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092369487 10000000000 1614397025369 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245563143/10000000000 : ℝ)^543 ≤ (42989911981723/100000000000000 : ℝ)^415 := by
    have hnat : (5245563143 : ℕ)^543*100000000000000^415 ≤ 42989911981723^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245563143 10000000000 42989911981723 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348301379/10000000000 : ℝ), (-2092369487/10000000000 : ℝ), (5245563143/10000000000 : ℝ)] ![(44094911799203/100000000000000 : ℝ), (1614397025369/12500000000000 : ℝ), (42989911981723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348301379/10000000000 : ℝ)|^543 ≤ (44094911799203/100000000000000 : ℝ)^415
        have hw : |(5348301379/10000000000 : ℝ)|=(5348301379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092369487/10000000000 : ℝ)|^543 ≤ (1614397025369/12500000000000 : ℝ)^415
        have hw : |(-2092369487/10000000000 : ℝ)|=(2092369487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245563143/10000000000 : ℝ)|^543 ≤ (42989911981723/100000000000000 : ℝ)^415
        have hw : |(5245563143/10000000000 : ℝ)|=(5245563143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348301389/10000000000 : ℝ)*x 0 + (655695391/1250000000 : ℝ)*x 1 + (-1046184747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348301389/10000000000 : ℝ)^543 ≤ (44094911907079/100000000000000 : ℝ)^415 := by
    have hnat : (5348301389 : ℕ)^543*100000000000000^415 ≤ 44094911907079^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348301389 10000000000 44094911907079 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655695391/1250000000 : ℝ)^543 ≤ (21494955910437/50000000000000 : ℝ)^415 := by
    have hnat : (655695391 : ℕ)^543*50000000000000^415 ≤ 21494955910437^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655695391 1250000000 21494955910437 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046184747/5000000000 : ℝ)^543 ≤ (6457588129743/50000000000000 : ℝ)^415 := by
    have hnat : (1046184747 : ℕ)^543*50000000000000^415 ≤ 6457588129743^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046184747 5000000000 6457588129743 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348301389/10000000000 : ℝ), (655695391/1250000000 : ℝ), (-1046184747/5000000000 : ℝ)] ![(44094911907079/100000000000000 : ℝ), (21494955910437/50000000000000 : ℝ), (6457588129743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348301389/10000000000 : ℝ)|^543 ≤ (44094911907079/100000000000000 : ℝ)^415
        have hw : |(5348301389/10000000000 : ℝ)|=(5348301389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655695391/1250000000 : ℝ)|^543 ≤ (21494955910437/50000000000000 : ℝ)^415
        have hw : |(655695391/1250000000 : ℝ)|=(655695391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046184747/5000000000 : ℝ)|^543 ≤ (6457588129743/50000000000000 : ℝ)^415
        have hw : |(-1046184747/5000000000 : ℝ)|=(1046184747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4315737513/10000000000 : ℝ)*x 0 + (828645299/2000000000 : ℝ)*x 1 + (4494817359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315737513/10000000000 : ℝ)^543 ≤ (33303791596289/100000000000000 : ℝ)^415 := by
    have hnat : (4315737513 : ℕ)^543*100000000000000^415 ≤ 33303791596289^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315737513 10000000000 33303791596289 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828645299/2000000000 : ℝ)^543 ≤ (15786396913117/50000000000000 : ℝ)^415 := by
    have hnat : (828645299 : ℕ)^543*50000000000000^415 ≤ 15786396913117^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828645299 2000000000 15786396913117 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494817359/10000000000 : ℝ)^543 ≤ (17561707282691/50000000000000 : ℝ)^415 := by
    have hnat : (4494817359 : ℕ)^543*50000000000000^415 ≤ 17561707282691^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494817359 10000000000 17561707282691 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315737513/10000000000 : ℝ), (828645299/2000000000 : ℝ), (4494817359/10000000000 : ℝ)] ![(33303791596289/100000000000000 : ℝ), (15786396913117/50000000000000 : ℝ), (17561707282691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315737513/10000000000 : ℝ)|^543 ≤ (33303791596289/100000000000000 : ℝ)^415
        have hw : |(4315737513/10000000000 : ℝ)|=(4315737513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828645299/2000000000 : ℝ)|^543 ≤ (15786396913117/50000000000000 : ℝ)^415
        have hw : |(828645299/2000000000 : ℝ)|=(828645299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494817359/10000000000 : ℝ)|^543 ≤ (17561707282691/50000000000000 : ℝ)^415
        have hw : |(4494817359/10000000000 : ℝ)|=(4494817359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-502054037/2500000000 : ℝ)*x 0 + (524615861/1000000000 : ℝ)*x 1 + (1082041541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502054037/2500000000 : ℝ)^543 ≤ (764986369347/6250000000000 : ℝ)^415 := by
    have hnat : (502054037 : ℕ)^543*6250000000000^415 ≤ 764986369347^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502054037 2500000000 764986369347 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524615861/1000000000 : ℝ)^543 ≤ (42996297431167/100000000000000 : ℝ)^415 := by
    have hnat : (524615861 : ℕ)^543*100000000000000^415 ≤ 42996297431167^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524615861 1000000000 42996297431167 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082041541/2000000000 : ℝ)^543 ≤ (44763920648077/100000000000000 : ℝ)^415 := by
    have hnat : (1082041541 : ℕ)^543*100000000000000^415 ≤ 44763920648077^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082041541 2000000000 44763920648077 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502054037/2500000000 : ℝ), (524615861/1000000000 : ℝ), (1082041541/2000000000 : ℝ)] ![(764986369347/6250000000000 : ℝ), (42996297431167/100000000000000 : ℝ), (44763920648077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502054037/2500000000 : ℝ)|^543 ≤ (764986369347/6250000000000 : ℝ)^415
        have hw : |(-502054037/2500000000 : ℝ)|=(502054037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524615861/1000000000 : ℝ)|^543 ≤ (42996297431167/100000000000000 : ℝ)^415
        have hw : |(524615861/1000000000 : ℝ)|=(524615861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082041541/2000000000 : ℝ)|^543 ≤ (44763920648077/100000000000000 : ℝ)^415
        have hw : |(1082041541/2000000000 : ℝ)|=(1082041541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652769883/5000000000 : ℝ)*x 0 + (-1927724903/10000000000 : ℝ)*x 1 + (5410207697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652769883/5000000000 : ℝ)^543 ≤ (5454273373303/12500000000000 : ℝ)^415 := by
    have hnat : (2652769883 : ℕ)^543*12500000000000^415 ≤ 5454273373303^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652769883 5000000000 5454273373303 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927724903/10000000000 : ℝ)^543 ≤ (5800946216917/50000000000000 : ℝ)^415 := by
    have hnat : (1927724903 : ℕ)^543*50000000000000^415 ≤ 5800946216917^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927724903 10000000000 5800946216917 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410207697/10000000000 : ℝ)^543 ≤ (44763920561469/100000000000000 : ℝ)^415 := by
    have hnat : (5410207697 : ℕ)^543*100000000000000^415 ≤ 44763920561469^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410207697 10000000000 44763920561469 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652769883/5000000000 : ℝ), (-1927724903/10000000000 : ℝ), (5410207697/10000000000 : ℝ)] ![(5454273373303/12500000000000 : ℝ), (5800946216917/50000000000000 : ℝ), (44763920561469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652769883/5000000000 : ℝ)|^543 ≤ (5454273373303/12500000000000 : ℝ)^415
        have hw : |(2652769883/5000000000 : ℝ)|=(2652769883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927724903/10000000000 : ℝ)|^543 ≤ (5800946216917/50000000000000 : ℝ)^415
        have hw : |(-1927724903/10000000000 : ℝ)|=(1927724903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410207697/10000000000 : ℝ)|^543 ≤ (44763920561469/100000000000000 : ℝ)^415
        have hw : |(5410207697/10000000000 : ℝ)|=(5410207697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305539741/10000000000 : ℝ)*x 0 + (2705103857/5000000000 : ℝ)*x 1 + (-963862457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305539741/10000000000 : ℝ)^543 ≤ (43634186717401/100000000000000 : ℝ)^415 := by
    have hnat : (5305539741 : ℕ)^543*100000000000000^415 ≤ 43634186717401^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305539741 10000000000 43634186717401 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705103857/5000000000 : ℝ)^543 ≤ (4476392074551/10000000000000 : ℝ)^415 := by
    have hnat : (2705103857 : ℕ)^543*10000000000000^415 ≤ 4476392074551^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705103857 5000000000 4476392074551 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963862457/5000000000 : ℝ)^543 ≤ (1450236565057/12500000000000 : ℝ)^415 := by
    have hnat : (963862457 : ℕ)^543*12500000000000^415 ≤ 1450236565057^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963862457 5000000000 1450236565057 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305539741/10000000000 : ℝ), (2705103857/5000000000 : ℝ), (-963862457/5000000000 : ℝ)] ![(43634186717401/100000000000000 : ℝ), (4476392074551/10000000000000 : ℝ), (1450236565057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305539741/10000000000 : ℝ)|^543 ≤ (43634186717401/100000000000000 : ℝ)^415
        have hw : |(5305539741/10000000000 : ℝ)|=(5305539741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705103857/5000000000 : ℝ)|^543 ≤ (4476392074551/10000000000000 : ℝ)^415
        have hw : |(2705103857/5000000000 : ℝ)|=(2705103857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-963862457/5000000000 : ℝ)|^543 ≤ (1450236565057/12500000000000 : ℝ)^415
        have hw : |(-963862457/5000000000 : ℝ)|=(963862457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s5_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4315762739/10000000000 : ℝ)*x 0 + (1123387591/2500000000 : ℝ)*x 1 + (207225003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315762739/10000000000 : ℝ)^543 ≤ (33304046302287/100000000000000 : ℝ)^415 := by
    have hnat : (4315762739 : ℕ)^543*100000000000000^415 ≤ 33304046302287^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315762739 10000000000 33304046302287 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123387591/2500000000 : ℝ)^543 ≤ (35110460907177/100000000000000 : ℝ)^415 := by
    have hnat : (1123387591 : ℕ)^543*100000000000000^415 ≤ 35110460907177^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123387591 2500000000 35110460907177 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207225003/500000000 : ℝ)^543 ≤ (1263419711001/4000000000000 : ℝ)^415 := by
    have hnat : (207225003 : ℕ)^543*4000000000000^415 ≤ 1263419711001^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207225003 500000000 1263419711001 4000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315762739/10000000000 : ℝ), (1123387591/2500000000 : ℝ), (207225003/500000000 : ℝ)] ![(33304046302287/100000000000000 : ℝ), (35110460907177/100000000000000 : ℝ), (1263419711001/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315762739/10000000000 : ℝ)|^543 ≤ (33304046302287/100000000000000 : ℝ)^415
        have hw : |(4315762739/10000000000 : ℝ)|=(4315762739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123387591/2500000000 : ℝ)|^543 ≤ (35110460907177/100000000000000 : ℝ)^415
        have hw : |(1123387591/2500000000 : ℝ)|=(1123387591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207225003/500000000 : ℝ)|^543 ≤ (1263419711001/4000000000000 : ℝ)^415
        have hw : |(207225003/500000000 : ℝ)|=(207225003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11207/100000 : ℝ) ^ (4343/1024 : ℝ) ≤ (2326076194725519/25000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^4343 ≤ (2326076194725519/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11207 : ℕ)^4343*25000000000000000000^1024 ≤ 2326076194725519^1024*100000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 2326076194725519 25000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (2326076194725519/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (4343/1024 : ℝ) ≤ (30020427371102219/100000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^4343 ≤ (30020427371102219/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3693 : ℕ)^4343*100000000000000000000^1024 ≤ 30020427371102219^1024*25000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 30020427371102219 100000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (30020427371102219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502326076194725519/12500000000000000000 : ℝ) ≤ (5000219362899039/5000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (12502326076194725519/12500000000000000000 : ℝ)^1024 ≤ (5000219362899039/5000000000000000 : ℝ)^4343 := by
      have hnat : (12502326076194725519 : ℕ)^1024*5000000000000000^4343 ≤ 5000219362899039^4343*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502326076194725519 12500000000000000000 5000219362899039 5000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000219362899039/5000000000000000 : ℝ)) (X := (12502326076194725519/12500000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007864946430000859/20000000000000000000 : ℝ) ≤ (1250115883249583/1250000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (20007864946430000859/20000000000000000000 : ℝ)^1024 ≤ (1250115883249583/1250000000000000 : ℝ)^4343 := by
      have hnat : (20007864946430000859 : ℕ)^1024*1250000000000000^4343 ≤ 1250115883249583^4343*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007864946430000859 20000000000000000000 1250115883249583 1250000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250115883249583/1250000000000000 : ℝ)) (X := (20007864946430000859/20000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030020427371102219/50000000000000000000 : ℝ) ≤ (40005661624781/40000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50030020427371102219/50000000000000000000 : ℝ)^1024 ≤ (40005661624781/40000000000000 : ℝ)^4343 := by
      have hnat : (50030020427371102219 : ℕ)^1024*40000000000000^4343 ≤ 40005661624781^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030020427371102219 50000000000000000000 40005661624781 40000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40005661624781/40000000000000 : ℝ)) (X := (50030020427371102219/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2326076194725519/25000000000000000000 : ℝ) ≤ ((17820309200129520733/17825000000000000000 : ℝ)+2*(244170099293/178250000000000 : ℝ)*(11207/100000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (17820309200129520733/17825000000000000000 : ℝ)+2*(244170099293/178250000000000 : ℝ)*(11207/100000 : ℝ)=(5000219362899039/5000000000000000 : ℝ) by norm_num, show 1+2*(2326076194725519/25000000000000000000 : ℝ)=(12502326076194725519/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30020427371102219/100000000000000000000 : ℝ)+(2326076194725519/25000000000000000000 : ℝ) ≤ ((17820309200129520733/17825000000000000000 : ℝ)+(244170099293/178250000000000 : ℝ)*((3693/25000 : ℝ)+(11207/100000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (17820309200129520733/17825000000000000000 : ℝ)+(244170099293/178250000000000 : ℝ)*((3693/25000 : ℝ)+(11207/100000 : ℝ))=(1250115883249583/1250000000000000 : ℝ) by norm_num, show 1+(30020427371102219/100000000000000000000 : ℝ)+(2326076194725519/25000000000000000000 : ℝ)=(20007864946430000859/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30020427371102219/100000000000000000000 : ℝ) ≤ ((17820309200129520733/17825000000000000000 : ℝ)+2*(244170099293/178250000000000 : ℝ)*(3693/25000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (17820309200129520733/17825000000000000000 : ℝ)+2*(244170099293/178250000000000 : ℝ)*(3693/25000 : ℝ)=(40005661624781/40000000000000 : ℝ) by norm_num, show 1+2*(30020427371102219/100000000000000000000 : ℝ)=(50030020427371102219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17820309200129520733/17825000000000000000 : ℝ)*(X 1 0+X 2 0)+(244170099293/178250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (17820309200129520733/17825000000000000000 : ℝ)) (alpha := (244170099293/178250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17820309200129520733/17825000000000000000 : ℝ)*(X 0 1+X 2 1)+(244170099293/178250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (17820309200129520733/17825000000000000000 : ℝ)) (alpha := (244170099293/178250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17820309200129520733/17825000000000000000 : ℝ)*(X 0 2+X 1 2)+(244170099293/178250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (17820309200129520733/17825000000000000000 : ℝ)) (alpha := (244170099293/178250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-502051071/2500000000 : ℝ)*X 0 0+(5410806281/10000000000 : ℝ)*X 0 1+(1311390781/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348301379/10000000000 : ℝ)*X 1 0+(-2092369487/10000000000 : ℝ)*X 1 1+(5245563143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348301389/10000000000 : ℝ)*X 2 0+(655695391/1250000000 : ℝ)*X 2 1+(-1046184747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315737513/10000000000 : ℝ)*X 0 0+(828645299/2000000000 : ℝ)*X 0 1+(4494817359/10000000000 : ℝ)*X 0 2+(4315737513/10000000000 : ℝ)*X 1 0+(828645299/2000000000 : ℝ)*X 1 1+(4494817359/10000000000 : ℝ)*X 1 2+(4315737513/10000000000 : ℝ)*X 2 0+(828645299/2000000000 : ℝ)*X 2 1+(4494817359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-502054037/2500000000 : ℝ)*X 0 0+(524615861/1000000000 : ℝ)*X 0 1+(1082041541/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652769883/5000000000 : ℝ)*X 1 0+(-1927724903/10000000000 : ℝ)*X 1 1+(5410207697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305539741/10000000000 : ℝ)*X 2 0+(2705103857/5000000000 : ℝ)*X 2 1+(-963862457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315762739/10000000000 : ℝ)*X 0 0+(1123387591/2500000000 : ℝ)*X 0 1+(207225003/500000000 : ℝ)*X 0 2+(4315762739/10000000000 : ℝ)*X 1 0+(1123387591/2500000000 : ℝ)*X 1 1+(207225003/500000000 : ℝ)*X 1 2+(4315762739/10000000000 : ℝ)*X 2 0+(1123387591/2500000000 : ℝ)*X 2 1+(207225003/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3617448558186547829971815639/445625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (748170687/50000000000000 : ℝ)*(base19) + (701015527/50000000000000 : ℝ)*(base23) + (56491751/100000000000000 : ℝ)*(lower2) + (208930239/100000000000000 : ℝ)*(upper3) + (62486387/50000000000000 : ℝ)*(upper5) + (4447998406521439/100000000000000 : ℝ)*(major0) + (4447998406521439/100000000000000 : ℝ)*(major1) + (4447998406521439/100000000000000 : ℝ)*(major2) + (3025860313711179/50000000000000 : ℝ)*(sp0) + (6051750349487541/100000000000000 : ℝ)*(sp1) + (3025875221898931/50000000000000 : ℝ)*(sp2) + (355528615634861/12500000000000 : ℝ)*(sp3) + (31218406557/100000000000000 : ℝ)*(sp4) + (788577259/5000000000000 : ℝ)*(sp7) + (711061174156017/25000000000000 : ℝ)*(f.failure) + (1210350369165783/20000000000000 : ℝ)*(f.sum) + (73257614783973/8912500000000000000000000000 : ℝ)*base66 + (12053088696962194787/1782500000000000000000000000000000 : ℝ)*base67 + (9141809483029694787/1782500000000000000000000000000000 : ℝ)*base69 + (28535379298174694787/1782500000000000000000000000000000 : ℝ)*base71 + (117417916266471/17825000000000000000000000000 : ℝ)*base74 + (3701910999265305213/1782500000000000000000000000000000 : ℝ)*base76 + (3052382693357194787/1782500000000000000000000000000000 : ℝ)*base77 + (18826239384002194787/1782500000000000000000000000000000 : ℝ)*base79 + (30146036879023/8912500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6008371/1250000000000000000000 : ℝ)*base89 + (6008371/1250000000000000000000 : ℝ)*base91 + (6008371/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1098708085513654299987031473/222812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (448477583/50000000000000 : ℝ)*(base19) + (9308991/1000000000000 : ℝ)*(base23) + (51780173/50000000000000 : ℝ)*(upper3) + (236179/781250000000 : ℝ)*(lower4) + (51285237/50000000000000 : ℝ)*(upper5) + (2240162912534573/50000000000000 : ℝ)*(major0) + (2240162912534573/50000000000000 : ℝ)*(major1) + (2240162912534573/50000000000000 : ℝ)*(major2) + (2302284301/12500000000000 : ℝ)*(sp1) + (9561958947/50000000000000 : ℝ)*(sp2) + (6095735224014317/100000000000000 : ℝ)*(sp4) + (6095715908784743/100000000000000 : ℝ)*(sp5) + (1523928792299331/25000000000000 : ℝ)*(sp6) + (716229065438591/25000000000000 : ℝ)*(sp7) + (716229065438591/25000000000000 : ℝ)*(f.failure) + (6095735224014317/100000000000000 : ℝ)*(f.sum) + (7030663275389/4456250000000000000000000000 : ℝ)*base65 + (8578754517899202009/891250000000000000000000000000000 : ℝ)*base67 + (878206161315452009/891250000000000000000000000000000 : ℝ)*base69 + (2931051304524202009/891250000000000000000000000000000 : ℝ)*base71 + (109194446601981/17825000000000000000000000000 : ℝ)*base73 + (970897293202952009/891250000000000000000000000000000 : ℝ)*base75 + (3530319711974202009/891250000000000000000000000000000 : ℝ)*base77 + (6809523774318297991/891250000000000000000000000000000 : ℝ)*base80 + (4943044579091/1114062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (164867/1250000000000000000000 : ℝ)*base90 + (164867/1250000000000000000000 : ℝ)*base92 + (164867/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1384_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1384_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1384_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1384_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1384_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
