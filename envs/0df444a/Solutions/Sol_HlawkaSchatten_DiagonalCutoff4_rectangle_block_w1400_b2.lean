-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1400_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:51.693128+00:00
-- url     : https://prove2.me/submissions/3bda9989-cc5d-4785-8f0a-933e2ef55e9c

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
theorem support_rectangle_w1400_s6_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994903823/10000000000 : ℝ)*x 0 + (5409716659/10000000000 : ℝ)*x 1 + (262310973/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994903823/10000000000 : ℝ)^545 ≤ (6081348717549/50000000000000 : ℝ)^417 := by
    have hnat : (1994903823 : ℕ)^545*50000000000000^417 ≤ 6081348717549^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994903823 10000000000 6081348717549 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409716659/10000000000 : ℝ)^545 ≤ (44799302651293/100000000000000 : ℝ)^417 := by
    have hnat : (5409716659 : ℕ)^545*100000000000000^417 ≤ 44799302651293^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409716659 10000000000 44799302651293 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262310973/500000000 : ℝ)^545 ≤ (10759499975683/25000000000000 : ℝ)^417 := by
    have hnat : (262310973 : ℕ)^545*25000000000000^417 ≤ 10759499975683^417*500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262310973 500000000 10759499975683 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994903823/10000000000 : ℝ), (5409716659/10000000000 : ℝ), (262310973/500000000 : ℝ)] ![(6081348717549/50000000000000 : ℝ), (44799302651293/100000000000000 : ℝ), (10759499975683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994903823/10000000000 : ℝ)|^545 ≤ (6081348717549/50000000000000 : ℝ)^417
        have hw : |(-1994903823/10000000000 : ℝ)|=(1994903823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409716659/10000000000 : ℝ)|^545 ≤ (44799302651293/100000000000000 : ℝ)^417
        have hw : |(5409716659/10000000000 : ℝ)|=(5409716659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262310973/500000000 : ℝ)|^545 ≤ (10759499975683/25000000000000 : ℝ)^417
        have hw : |(262310973/500000000 : ℝ)|=(262310973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347921239/10000000000 : ℝ)*x 0 + (-32471303/156250000 : ℝ)*x 1 + (5246219461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347921239/10000000000 : ℝ)^545 ≤ (11032912958599/25000000000000 : ℝ)^417 := by
    have hnat : (5347921239 : ℕ)^545*25000000000000^417 ≤ 11032912958599^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347921239 10000000000 11032912958599 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32471303/156250000 : ℝ)^545 ≤ (3207587059523/25000000000000 : ℝ)^417 := by
    have hnat : (32471303 : ℕ)^545*25000000000000^417 ≤ 3207587059523^417*156250000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32471303 156250000 3207587059523 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246219461/10000000000 : ℝ)^545 ≤ (21518999956727/50000000000000 : ℝ)^417 := by
    have hnat : (5246219461 : ℕ)^545*50000000000000^417 ≤ 21518999956727^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246219461 10000000000 21518999956727 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347921239/10000000000 : ℝ), (-32471303/156250000 : ℝ), (5246219461/10000000000 : ℝ)] ![(11032912958599/25000000000000 : ℝ), (3207587059523/25000000000000 : ℝ), (21518999956727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347921239/10000000000 : ℝ)|^545 ≤ (11032912958599/25000000000000 : ℝ)^417
        have hw : |(5347921239/10000000000 : ℝ)|=(5347921239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32471303/156250000 : ℝ)|^545 ≤ (3207587059523/25000000000000 : ℝ)^417
        have hw : |(-32471303/156250000 : ℝ)|=(32471303/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246219461/10000000000 : ℝ)|^545 ≤ (21518999956727/50000000000000 : ℝ)^417
        have hw : |(5246219461/10000000000 : ℝ)|=(5246219461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347921239/10000000000 : ℝ)*x 0 + (5246219461/10000000000 : ℝ)*x 1 + (-32471303/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347921239/10000000000 : ℝ)^545 ≤ (11032912958599/25000000000000 : ℝ)^417 := by
    have hnat : (5347921239 : ℕ)^545*25000000000000^417 ≤ 11032912958599^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347921239 10000000000 11032912958599 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246219461/10000000000 : ℝ)^545 ≤ (21518999956727/50000000000000 : ℝ)^417 := by
    have hnat : (5246219461 : ℕ)^545*50000000000000^417 ≤ 21518999956727^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246219461 10000000000 21518999956727 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32471303/156250000 : ℝ)^545 ≤ (3207587059523/25000000000000 : ℝ)^417 := by
    have hnat : (32471303 : ℕ)^545*25000000000000^417 ≤ 3207587059523^417*156250000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32471303 156250000 3207587059523 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347921239/10000000000 : ℝ), (5246219461/10000000000 : ℝ), (-32471303/156250000 : ℝ)] ![(11032912958599/25000000000000 : ℝ), (21518999956727/50000000000000 : ℝ), (3207587059523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347921239/10000000000 : ℝ)|^545 ≤ (11032912958599/25000000000000 : ℝ)^417
        have hw : |(5347921239/10000000000 : ℝ)|=(5347921239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246219461/10000000000 : ℝ)|^545 ≤ (21518999956727/50000000000000 : ℝ)^417
        have hw : |(5246219461/10000000000 : ℝ)|=(5246219461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32471303/156250000 : ℝ)|^545 ≤ (3207587059523/25000000000000 : ℝ)^417
        have hw : |(-32471303/156250000 : ℝ)|=(32471303/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (269479903/625000000 : ℝ)*x 0 + (2069970117/5000000000 : ℝ)*x 1 + (2244942367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269479903/625000000 : ℝ)^545 ≤ (33304233737533/100000000000000 : ℝ)^417 := by
    have hnat : (269479903 : ℕ)^545*100000000000000^417 ≤ 33304233737533^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269479903 625000000 33304233737533 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069970117/5000000000 : ℝ)^545 ≤ (31581205421937/100000000000000 : ℝ)^417 := by
    have hnat : (2069970117 : ℕ)^545*100000000000000^417 ≤ 31581205421937^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069970117 5000000000 31581205421937 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244942367/5000000000 : ℝ)^545 ≤ (17557280410491/50000000000000 : ℝ)^417 := by
    have hnat : (2244942367 : ℕ)^545*50000000000000^417 ≤ 17557280410491^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244942367 5000000000 17557280410491 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269479903/625000000 : ℝ), (2069970117/5000000000 : ℝ), (2244942367/5000000000 : ℝ)] ![(33304233737533/100000000000000 : ℝ), (31581205421937/100000000000000 : ℝ), (17557280410491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269479903/625000000 : ℝ)|^545 ≤ (33304233737533/100000000000000 : ℝ)^417
        have hw : |(269479903/625000000 : ℝ)|=(269479903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069970117/5000000000 : ℝ)|^545 ≤ (31581205421937/100000000000000 : ℝ)^417
        have hw : |(2069970117/5000000000 : ℝ)|=(2069970117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244942367/5000000000 : ℝ)|^545 ≤ (17557280410491/50000000000000 : ℝ)^417
        have hw : |(2244942367/5000000000 : ℝ)|=(2244942367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994915479/10000000000 : ℝ)*x 0 + (209872303/400000000 : ℝ)*x 1 + (338070341/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994915479/10000000000 : ℝ)^545 ≤ (2432558062853/20000000000000 : ℝ)^417 := by
    have hnat : (1994915479 : ℕ)^545*20000000000000^417 ≤ 2432558062853^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994915479 10000000000 2432558062853 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209872303/400000000 : ℝ)^545 ≤ (5380538204873/12500000000000 : ℝ)^417 := by
    have hnat : (209872303 : ℕ)^545*12500000000000^417 ≤ 5380538204873^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209872303 400000000 5380538204873 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338070341/625000000 : ℝ)^545 ≤ (8958580805647/20000000000000 : ℝ)^417 := by
    have hnat : (338070341 : ℕ)^545*20000000000000^417 ≤ 8958580805647^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338070341 625000000 8958580805647 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994915479/10000000000 : ℝ), (209872303/400000000 : ℝ), (338070341/625000000 : ℝ)] ![(2432558062853/20000000000000 : ℝ), (5380538204873/12500000000000 : ℝ), (8958580805647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994915479/10000000000 : ℝ)|^545 ≤ (2432558062853/20000000000000 : ℝ)^417
        have hw : |(-1994915479/10000000000 : ℝ)|=(1994915479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209872303/400000000 : ℝ)|^545 ≤ (5380538204873/12500000000000 : ℝ)^417
        have hw : |(209872303/400000000 : ℝ)|=(209872303/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338070341/625000000 : ℝ)|^545 ≤ (8958580805647/20000000000000 : ℝ)^417
        have hw : |(338070341/625000000 : ℝ)|=(338070341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305540283/10000000000 : ℝ)*x 0 + (-1915257387/10000000000 : ℝ)*x 1 + (5409125401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305540283/10000000000 : ℝ)^545 ≤ (1091878110419/2500000000000 : ℝ)^417 := by
    have hnat : (5305540283 : ℕ)^545*2500000000000^417 ≤ 1091878110419^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305540283 10000000000 1091878110419 2500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915257387/10000000000 : ℝ)^545 ≤ (11531972131081/100000000000000 : ℝ)^417 := by
    have hnat : (1915257387 : ℕ)^545*100000000000000^417 ≤ 11531972131081^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915257387 10000000000 11531972131081 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409125401/10000000000 : ℝ)^545 ≤ (44792903432977/100000000000000 : ℝ)^417 := by
    have hnat : (5409125401 : ℕ)^545*100000000000000^417 ≤ 44792903432977^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409125401 10000000000 44792903432977 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305540283/10000000000 : ℝ), (-1915257387/10000000000 : ℝ), (5409125401/10000000000 : ℝ)] ![(1091878110419/2500000000000 : ℝ), (11531972131081/100000000000000 : ℝ), (44792903432977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305540283/10000000000 : ℝ)|^545 ≤ (1091878110419/2500000000000 : ℝ)^417
        have hw : |(5305540283/10000000000 : ℝ)|=(5305540283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1915257387/10000000000 : ℝ)|^545 ≤ (11531972131081/100000000000000 : ℝ)^417
        have hw : |(-1915257387/10000000000 : ℝ)|=(1915257387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409125401/10000000000 : ℝ)|^545 ≤ (44792903432977/100000000000000 : ℝ)^417
        have hw : |(5409125401/10000000000 : ℝ)|=(5409125401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (331596269/625000000 : ℝ)*x 0 + (2704562683/5000000000 : ℝ)*x 1 + (-1915257407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331596269/625000000 : ℝ)^545 ≤ (5459390580337/12500000000000 : ℝ)^417 := by
    have hnat : (331596269 : ℕ)^545*12500000000000^417 ≤ 5459390580337^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331596269 625000000 5459390580337 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704562683/5000000000 : ℝ)^545 ≤ (1399778220443/3125000000000 : ℝ)^417 := by
    have hnat : (2704562683 : ℕ)^545*3125000000000^417 ≤ 1399778220443^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704562683 5000000000 1399778220443 3125000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915257407/10000000000 : ℝ)^545 ≤ (11531972288467/100000000000000 : ℝ)^417 := by
    have hnat : (1915257407 : ℕ)^545*100000000000000^417 ≤ 11531972288467^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915257407 10000000000 11531972288467 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331596269/625000000 : ℝ), (2704562683/5000000000 : ℝ), (-1915257407/10000000000 : ℝ)] ![(5459390580337/12500000000000 : ℝ), (1399778220443/3125000000000 : ℝ), (11531972288467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331596269/625000000 : ℝ)|^545 ≤ (5459390580337/12500000000000 : ℝ)^417
        have hw : |(331596269/625000000 : ℝ)|=(331596269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704562683/5000000000 : ℝ)|^545 ≤ (1399778220443/3125000000000 : ℝ)^417
        have hw : |(2704562683/5000000000 : ℝ)|=(2704562683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915257407/10000000000 : ℝ)|^545 ≤ (11531972288467/100000000000000 : ℝ)^417
        have hw : |(-1915257407/10000000000 : ℝ)|=(1915257407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s6_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1077925829/2500000000 : ℝ)*x 0 + (897725151/2000000000 : ℝ)*x 1 + (414120567/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077925829/2500000000 : ℝ)^545 ≤ (1665224239219/5000000000000 : ℝ)^417 := by
    have hnat : (1077925829 : ℕ)^545*5000000000000^417 ≤ 1665224239219^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077925829 2500000000 1665224239219 5000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897725151/2000000000 : ℝ)^545 ≤ (877542319607/2500000000000 : ℝ)^417 := by
    have hnat : (897725151 : ℕ)^545*2500000000000^417 ≤ 877542319607^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897725151 2000000000 877542319607 2500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414120567/1000000000 : ℝ)^545 ≤ (31593822408361/100000000000000 : ℝ)^417 := by
    have hnat : (414120567 : ℕ)^545*100000000000000^417 ≤ 31593822408361^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414120567 1000000000 31593822408361 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077925829/2500000000 : ℝ), (897725151/2000000000 : ℝ), (414120567/1000000000 : ℝ)] ![(1665224239219/5000000000000 : ℝ), (877542319607/2500000000000 : ℝ), (31593822408361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077925829/2500000000 : ℝ)|^545 ≤ (1665224239219/5000000000000 : ℝ)^417
        have hw : |(1077925829/2500000000 : ℝ)|=(1077925829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897725151/2000000000 : ℝ)|^545 ≤ (877542319607/2500000000000 : ℝ)^417
        have hw : |(897725151/2000000000 : ℝ)|=(897725151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414120567/1000000000 : ℝ)|^545 ≤ (31593822408361/100000000000000 : ℝ)^417
        have hw : |(414120567/1000000000 : ℝ)|=(414120567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7371/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (451/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (451/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (451/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7373/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (451/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (451/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7373/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (451/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (451/4000 : ℝ) ^ (4359/1024 : ℝ) ≤ (9226047108923787/100000000000000000000 : ℝ) := by
    have hpowers : (451/4000 : ℝ)^4359 ≤ (9226047108923787/100000000000000000000 : ℝ)^1024 := by
      have hnat : (451 : ℕ)^4359*100000000000000000000^1024 ≤ 9226047108923787^1024*4000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        451 4000 9226047108923787 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (451/4000 : ℝ)) (X := (9226047108923787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7373/50000 : ℝ) ^ (4359/1024 : ℝ) ≤ (3614869284939231/12500000000000000000 : ℝ) := by
    have hpowers : (7373/50000 : ℝ)^4359 ≤ (3614869284939231/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7373 : ℕ)^4359*12500000000000000000^1024 ≤ 3614869284939231^1024*50000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7373 50000 3614869284939231 12500000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7373/50000 : ℝ)) (X := (3614869284939231/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009226047108923787/50000000000000000000 : ℝ) ≤ (10000433439111877/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50009226047108923787/50000000000000000000 : ℝ)^1024 ≤ (10000433439111877/10000000000000000 : ℝ)^4359 := by
      have hnat : (50009226047108923787 : ℕ)^1024*10000000000000000^4359 ≤ 10000433439111877^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009226047108923787 50000000000000000000 10000433439111877 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433439111877/10000000000000000 : ℝ)) (X := (50009226047108923787/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007629000277687527/20000000000000000000 : ℝ) ≤ (10000895957397837/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (20007629000277687527/20000000000000000000 : ℝ)^1024 ≤ (10000895957397837/10000000000000000 : ℝ)^4359 := by
      have hnat : (20007629000277687527 : ℕ)^1024*10000000000000000^4359 ≤ 10000895957397837^4359*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007629000277687527 20000000000000000000 10000895957397837 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000895957397837/10000000000000000 : ℝ)) (X := (20007629000277687527/20000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253614869284939231/6250000000000000000 : ℝ) ≤ (10001358475683797/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (6253614869284939231/6250000000000000000 : ℝ)^1024 ≤ (10001358475683797/10000000000000000 : ℝ)^4359 := by
      have hnat : (6253614869284939231 : ℕ)^1024*10000000000000000^4359 ≤ 10001358475683797^4359*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253614869284939231 6250000000000000000 10001358475683797 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001358475683797/10000000000000000 : ℝ)) (X := (6253614869284939231/6250000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9226047108923787/100000000000000000000 : ℝ) ≤ ((34701074679808927067/34710000000000000000 : ℝ)+2*(11562957149/8677500000000 : ℝ)*(451/4000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (34701074679808927067/34710000000000000000 : ℝ)+2*(11562957149/8677500000000 : ℝ)*(451/4000 : ℝ)=(10000433439111877/10000000000000000 : ℝ) by norm_num, show 1+2*(9226047108923787/100000000000000000000 : ℝ)=(50009226047108923787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3614869284939231/12500000000000000000 : ℝ)+(9226047108923787/100000000000000000000 : ℝ) ≤ ((34701074679808927067/34710000000000000000 : ℝ)+(11562957149/8677500000000 : ℝ)*((7373/50000 : ℝ)+(451/4000 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (34701074679808927067/34710000000000000000 : ℝ)+(11562957149/8677500000000 : ℝ)*((7373/50000 : ℝ)+(451/4000 : ℝ))=(10000895957397837/10000000000000000 : ℝ) by norm_num, show 1+(3614869284939231/12500000000000000000 : ℝ)+(9226047108923787/100000000000000000000 : ℝ)=(20007629000277687527/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3614869284939231/12500000000000000000 : ℝ) ≤ ((34701074679808927067/34710000000000000000 : ℝ)+2*(11562957149/8677500000000 : ℝ)*(7373/50000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (34701074679808927067/34710000000000000000 : ℝ)+2*(11562957149/8677500000000 : ℝ)*(7373/50000 : ℝ)=(10001358475683797/10000000000000000 : ℝ) by norm_num, show 1+2*(3614869284939231/12500000000000000000 : ℝ)=(6253614869284939231/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34701074679808927067/34710000000000000000 : ℝ)*(X 1 0+X 2 0)+(11562957149/8677500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (451/4000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (34701074679808927067/34710000000000000000 : ℝ)) (alpha := (11562957149/8677500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34701074679808927067/34710000000000000000 : ℝ)*(X 0 1+X 2 1)+(11562957149/8677500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (451/4000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (34701074679808927067/34710000000000000000 : ℝ)) (alpha := (11562957149/8677500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34701074679808927067/34710000000000000000 : ℝ)*(X 0 2+X 1 2)+(11562957149/8677500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (451/4000 : ℝ)) (hi := (7373/50000 : ℝ)) (c := (34701074679808927067/34710000000000000000 : ℝ)) (alpha := (11562957149/8677500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1994903823/10000000000 : ℝ)*X 0 0+(5409716659/10000000000 : ℝ)*X 0 1+(262310973/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347921239/10000000000 : ℝ)*X 1 0+(-32471303/156250000 : ℝ)*X 1 1+(5246219461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347921239/10000000000 : ℝ)*X 2 0+(5246219461/10000000000 : ℝ)*X 2 1+(-32471303/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269479903/625000000 : ℝ)*X 0 0+(2069970117/5000000000 : ℝ)*X 0 1+(2244942367/5000000000 : ℝ)*X 0 2+(269479903/625000000 : ℝ)*X 1 0+(2069970117/5000000000 : ℝ)*X 1 1+(2244942367/5000000000 : ℝ)*X 1 2+(269479903/625000000 : ℝ)*X 2 0+(2069970117/5000000000 : ℝ)*X 2 1+(2244942367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994915479/10000000000 : ℝ)*X 0 0+(209872303/400000000 : ℝ)*X 0 1+(338070341/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305540283/10000000000 : ℝ)*X 1 0+(-1915257387/10000000000 : ℝ)*X 1 1+(5409125401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331596269/625000000 : ℝ)*X 2 0+(2704562683/5000000000 : ℝ)*X 2 1+(-1915257407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077925829/2500000000 : ℝ)*X 0 0+(897725151/2000000000 : ℝ)*X 0 1+(414120567/1000000000 : ℝ)*X 0 2+(1077925829/2500000000 : ℝ)*X 1 0+(897725151/2000000000 : ℝ)*X 1 1+(414120567/1000000000 : ℝ)*X 1 2+(1077925829/2500000000 : ℝ)*X 2 0+(897725151/2000000000 : ℝ)*X 2 1+(414120567/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (473708740899264662716810341/57850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1504266839/100000000000000 : ℝ)*(base19) + (701184811/50000000000000 : ℝ)*(base23) + (5449383/10000000000000 : ℝ)*(lower2) + (204378989/100000000000000 : ℝ)*(upper3) + (16241149/12500000000000 : ℝ)*(upper5) + (897400320533423/20000000000000 : ℝ)*(major0) + (897400320533423/20000000000000 : ℝ)*(major1) + (897400320533423/20000000000000 : ℝ)*(major2) + (764543185631383/12500000000000 : ℝ)*(sp0) + (6116375368707507/100000000000000 : ℝ)*(sp1) + (1529093867651181/25000000000000 : ℝ)*(sp2) + (1428805103229247/50000000000000 : ℝ)*(sp3) + (15693961641/50000000000000 : ℝ)*(sp4) + (15852949063/100000000000000 : ℝ)*(sp7) + (714406514851889/25000000000000 : ℝ)*(f.failure) + (3058188436487173/50000000000000 : ℝ)*(f.sum) + (2521246547971/347100000000000000000000000 : ℝ)*base65 + (3728584109424539659/694200000000000000000000000000000 : ℝ)*base68 + (4843114122688739659/694200000000000000000000000000000 : ℝ)*base70 + (3778198518169739659/694200000000000000000000000000000 : ℝ)*base72 + (14830180542673/3471000000000000000000000000 : ℝ)*base73 + (9666708463357739659/694200000000000000000000000000000 : ℝ)*base76 + (2477035070535660341/694200000000000000000000000000000 : ℝ)*base77 + (18018272810884139659/694200000000000000000000000000000 : ℝ)*base80 + (5374455842989/1735500000000000000000000000 : ℝ)*base82 + (27201611/2500000000000000000000 : ℝ)*base90 + (27201611/2500000000000000000000 : ℝ)*base92 + (27201611/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1415851725503632259408231013/144625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247170779/12500000000000 : ℝ)*(base19) + (41490501/2000000000000 : ℝ)*(base23) + (165886817/25000000000000 : ℝ)*(lower1) + (197060213/100000000000000 : ℝ)*(upper3) + (21034337/50000000000000 : ℝ)*(lower4) + (257081991/100000000000000 : ℝ)*(upper5) + (2259762782661239/50000000000000 : ℝ)*(major0) + (2259762782661239/50000000000000 : ℝ)*(major1) + (2259762782661239/50000000000000 : ℝ)*(major2) + (407985361/50000000000000 : ℝ)*(sp1) + (6160711286019631/100000000000000 : ℝ)*(sp4) + (6160708492682677/100000000000000 : ℝ)*(sp5) + (6160709211494581/100000000000000 : ℝ)*(sp6) + (575667903659643/20000000000000 : ℝ)*(sp7) + (575667903659643/20000000000000 : ℝ)*(f.failure) + (6160711286019631/100000000000000 : ℝ)*(f.sum) + (579793062263/694200000000000000000000000 : ℝ)*base65 + (14639775210362143987/1735500000000000000000000000000000 : ℝ)*base68 + (19176152905640143987/1735500000000000000000000000000000 : ℝ)*base70 + (7782625434996643987/1735500000000000000000000000000000 : ℝ)*base72 + (5733528635267/1735500000000000000000000000 : ℝ)*base73 + (17784581423436643987/1735500000000000000000000000000000 : ℝ)*base76 + (7095207815640856013/1735500000000000000000000000000000 : ℝ)*base77 + (6533492163207643987/1735500000000000000000000000000000 : ℝ)*base80 + (6804752818817/3471000000000000000000000000 : ℝ)*base82 + (1944857/2000000000000000000000 : ℝ)*base90 + (1944857/2000000000000000000000 : ℝ)*base92 + (1944857/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1400_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1400_s7_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994906553/10000000000 : ℝ)*x 0 + (5409686523/10000000000 : ℝ)*x 1 + (1311561963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994906553/10000000000 : ℝ)^545 ≤ (12162719188697/100000000000000 : ℝ)^417 := by
    have hnat : (1994906553 : ℕ)^545*100000000000000^417 ≤ 12162719188697^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994906553 10000000000 12162719188697 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409686523/10000000000 : ℝ)^545 ≤ (11199744120623/25000000000000 : ℝ)^417 := by
    have hnat : (5409686523 : ℕ)^545*25000000000000^417 ≤ 11199744120623^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409686523 10000000000 11199744120623 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311561963/2500000000 : ℝ)^545 ≤ (43038304315189/100000000000000 : ℝ)^417 := by
    have hnat : (1311561963 : ℕ)^545*100000000000000^417 ≤ 43038304315189^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311561963 2500000000 43038304315189 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994906553/10000000000 : ℝ), (5409686523/10000000000 : ℝ), (1311561963/2500000000 : ℝ)] ![(12162719188697/100000000000000 : ℝ), (11199744120623/25000000000000 : ℝ), (43038304315189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994906553/10000000000 : ℝ)|^545 ≤ (12162719188697/100000000000000 : ℝ)^417
        have hw : |(-1994906553/10000000000 : ℝ)|=(1994906553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409686523/10000000000 : ℝ)|^545 ≤ (11199744120623/25000000000000 : ℝ)^417
        have hw : |(5409686523/10000000000 : ℝ)|=(5409686523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311561963/2500000000 : ℝ)|^545 ≤ (43038304315189/100000000000000 : ℝ)^417
        have hw : |(1311561963/2500000000 : ℝ)|=(1311561963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (42783307/80000000 : ℝ)*x 0 + (-2078136329/10000000000 : ℝ)*x 1 + (5246247739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42783307/80000000 : ℝ)^545 ≤ (8826313404021/20000000000000 : ℝ)^417 := by
    have hnat : (42783307 : ℕ)^545*20000000000000^417 ≤ 8826313404021^417*80000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42783307 80000000 8826313404021 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078136329/10000000000 : ℝ)^545 ≤ (160376623343/1250000000000 : ℝ)^417 := by
    have hnat : (2078136329 : ℕ)^545*1250000000000^417 ≤ 160376623343^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078136329 10000000000 160376623343 1250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246247739/10000000000 : ℝ)^545 ≤ (10759575775907/25000000000000 : ℝ)^417 := by
    have hnat : (5246247739 : ℕ)^545*25000000000000^417 ≤ 10759575775907^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246247739 10000000000 10759575775907 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42783307/80000000 : ℝ), (-2078136329/10000000000 : ℝ), (5246247739/10000000000 : ℝ)] ![(8826313404021/20000000000000 : ℝ), (160376623343/1250000000000 : ℝ), (10759575775907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42783307/80000000 : ℝ)|^545 ≤ (8826313404021/20000000000000 : ℝ)^417
        have hw : |(42783307/80000000 : ℝ)|=(42783307/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078136329/10000000000 : ℝ)|^545 ≤ (160376623343/1250000000000 : ℝ)^417
        have hw : |(-2078136329/10000000000 : ℝ)|=(2078136329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246247739/10000000000 : ℝ)|^545 ≤ (10759575775907/25000000000000 : ℝ)^417
        have hw : |(5246247739/10000000000 : ℝ)|=(5246247739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347913783/10000000000 : ℝ)*x 0 + (5246247573/10000000000 : ℝ)*x 1 + (-519534001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347913783/10000000000 : ℝ)^545 ≤ (22065785710219/50000000000000 : ℝ)^417 := by
    have hnat : (5347913783 : ℕ)^545*50000000000000^417 ≤ 22065785710219^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347913783 10000000000 22065785710219 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246247573/10000000000 : ℝ)^545 ≤ (43038301323813/100000000000000 : ℝ)^417 := by
    have hnat : (5246247573 : ℕ)^545*100000000000000^417 ≤ 43038301323813^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246247573 10000000000 43038301323813 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519534001/2500000000 : ℝ)^545 ≤ (3207531811257/25000000000000 : ℝ)^417 := by
    have hnat : (519534001 : ℕ)^545*25000000000000^417 ≤ 3207531811257^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519534001 2500000000 3207531811257 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347913783/10000000000 : ℝ), (5246247573/10000000000 : ℝ), (-519534001/2500000000 : ℝ)] ![(22065785710219/50000000000000 : ℝ), (43038301323813/100000000000000 : ℝ), (3207531811257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347913783/10000000000 : ℝ)|^545 ≤ (22065785710219/50000000000000 : ℝ)^417
        have hw : |(5347913783/10000000000 : ℝ)|=(5347913783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246247573/10000000000 : ℝ)|^545 ≤ (43038301323813/100000000000000 : ℝ)^417
        have hw : |(5246247573/10000000000 : ℝ)|=(5246247573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519534001/2500000000 : ℝ)|^545 ≤ (3207531811257/25000000000000 : ℝ)^417
        have hw : |(-519534001/2500000000 : ℝ)|=(519534001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4311680351/10000000000 : ℝ)*x 0 + (4140002819/10000000000 : ℝ)*x 1 + (4489821809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311680351/10000000000 : ℝ)^545 ≤ (16652126474319/50000000000000 : ℝ)^417 := by
    have hnat : (4311680351 : ℕ)^545*50000000000000^417 ≤ 16652126474319^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311680351 10000000000 16652126474319 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4140002819/10000000000 : ℝ)^545 ≤ (789545734893/2500000000000 : ℝ)^417 := by
    have hnat : (4140002819 : ℕ)^545*2500000000000^417 ≤ 789545734893^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140002819 10000000000 789545734893 2500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489821809/10000000000 : ℝ)^545 ≤ (17556958818821/50000000000000 : ℝ)^417 := by
    have hnat : (4489821809 : ℕ)^545*50000000000000^417 ≤ 17556958818821^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489821809 10000000000 17556958818821 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311680351/10000000000 : ℝ), (4140002819/10000000000 : ℝ), (4489821809/10000000000 : ℝ)] ![(16652126474319/50000000000000 : ℝ), (789545734893/2500000000000 : ℝ), (17556958818821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311680351/10000000000 : ℝ)|^545 ≤ (16652126474319/50000000000000 : ℝ)^417
        have hw : |(4311680351/10000000000 : ℝ)|=(4311680351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4140002819/10000000000 : ℝ)|^545 ≤ (789545734893/2500000000000 : ℝ)^417
        have hw : |(4140002819/10000000000 : ℝ)|=(4140002819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489821809/10000000000 : ℝ)|^545 ≤ (17556958818821/50000000000000 : ℝ)^417
        have hw : |(4489821809/10000000000 : ℝ)|=(4489821809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-398983659/2000000000 : ℝ)*x 0 + (2623417749/5000000000 : ℝ)*x 1 + (135227393/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398983659/2000000000 : ℝ)^545 ≤ (12162812753183/100000000000000 : ℝ)^417 := by
    have hnat : (398983659 : ℕ)^545*100000000000000^417 ≤ 12162812753183^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398983659 2000000000 12162812753183 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623417749/5000000000 : ℝ)^545 ≤ (43044605033229/100000000000000 : ℝ)^417 := by
    have hnat : (2623417749 : ℕ)^545*100000000000000^417 ≤ 43044605033229^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623417749 5000000000 43044605033229 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135227393/250000000 : ℝ)^545 ≤ (44792582199517/100000000000000 : ℝ)^417 := by
    have hnat : (135227393 : ℕ)^545*100000000000000^417 ≤ 44792582199517^417*250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135227393 250000000 44792582199517 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398983659/2000000000 : ℝ), (2623417749/5000000000 : ℝ), (135227393/250000000 : ℝ)] ![(12162812753183/100000000000000 : ℝ), (43044605033229/100000000000000 : ℝ), (44792582199517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398983659/2000000000 : ℝ)|^545 ≤ (12162812753183/100000000000000 : ℝ)^417
        have hw : |(-398983659/2000000000 : ℝ)|=(398983659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623417749/5000000000 : ℝ)|^545 ≤ (43044605033229/100000000000000 : ℝ)^417
        have hw : |(2623417749/5000000000 : ℝ)|=(2623417749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135227393/250000000 : ℝ)|^545 ≤ (44792582199517/100000000000000 : ℝ)^417
        have hw : |(135227393/250000000 : ℝ)|=(135227393/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (21222191/40000000 : ℝ)*x 0 + (-191528801/1000000000 : ℝ)*x 1 + (5409095713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21222191/40000000 : ℝ)^545 ≤ (43675204752949/100000000000000 : ℝ)^417 := by
    have hnat : (21222191 : ℕ)^545*100000000000000^417 ≤ 43675204752949^417*40000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21222191 40000000 43675204752949 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191528801/1000000000 : ℝ)^545 ≤ (11532213113681/100000000000000 : ℝ)^417 := by
    have hnat : (191528801 : ℕ)^545*100000000000000^417 ≤ 11532213113681^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191528801 1000000000 11532213113681 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409095713/10000000000 : ℝ)^545 ≤ (22396291061879/50000000000000 : ℝ)^417 := by
    have hnat : (5409095713 : ℕ)^545*50000000000000^417 ≤ 22396291061879^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409095713 10000000000 22396291061879 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21222191/40000000 : ℝ), (-191528801/1000000000 : ℝ), (5409095713/10000000000 : ℝ)] ![(43675204752949/100000000000000 : ℝ), (11532213113681/100000000000000 : ℝ), (22396291061879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21222191/40000000 : ℝ)|^545 ≤ (43675204752949/100000000000000 : ℝ)^417
        have hw : |(21222191/40000000 : ℝ)|=(21222191/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191528801/1000000000 : ℝ)|^545 ≤ (11532213113681/100000000000000 : ℝ)^417
        have hw : |(-191528801/1000000000 : ℝ)|=(191528801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409095713/10000000000 : ℝ)|^545 ≤ (22396291061879/50000000000000 : ℝ)^417
        have hw : |(5409095713/10000000000 : ℝ)|=(5409095713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652773873/5000000000 : ℝ)*x 0 + (2704547859/5000000000 : ℝ)*x 1 + (-239411001/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652773873/5000000000 : ℝ)^545 ≤ (21837602354957/50000000000000 : ℝ)^417 := by
    have hnat : (2652773873 : ℕ)^545*50000000000000^417 ≤ 21837602354957^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652773873 5000000000 21837602354957 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704547859/5000000000 : ℝ)^545 ≤ (2799536386117/6250000000000 : ℝ)^417 := by
    have hnat : (2704547859 : ℕ)^545*6250000000000^417 ≤ 2799536386117^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704547859 5000000000 2799536386117 6250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239411001/1250000000 : ℝ)^545 ≤ (5766106548971/50000000000000 : ℝ)^417 := by
    have hnat : (239411001 : ℕ)^545*50000000000000^417 ≤ 5766106548971^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239411001 1250000000 5766106548971 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652773873/5000000000 : ℝ), (2704547859/5000000000 : ℝ), (-239411001/1250000000 : ℝ)] ![(21837602354957/50000000000000 : ℝ), (2799536386117/6250000000000 : ℝ), (5766106548971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652773873/5000000000 : ℝ)|^545 ≤ (21837602354957/50000000000000 : ℝ)^417
        have hw : |(2652773873/5000000000 : ℝ)|=(2652773873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704547859/5000000000 : ℝ)|^545 ≤ (2799536386117/6250000000000 : ℝ)^417
        have hw : |(2704547859/5000000000 : ℝ)|=(2704547859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239411001/1250000000 : ℝ)|^545 ≤ (5766106548971/50000000000000 : ℝ)^417
        have hw : |(-239411001/1250000000 : ℝ)|=(239411001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_s7_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4311705293/10000000000 : ℝ)*x 0 + (1122140983/2500000000 : ℝ)*x 1 + (25882919/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311705293/10000000000 : ℝ)^545 ≤ (16652252371281/50000000000000 : ℝ)^417 := by
    have hnat : (4311705293 : ℕ)^545*50000000000000^417 ≤ 16652252371281^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311705293 10000000000 16652252371281 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122140983/2500000000 : ℝ)^545 ≤ (1404042436773/4000000000000 : ℝ)^417 := by
    have hnat : (1122140983 : ℕ)^545*4000000000000^417 ≤ 1404042436773^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122140983 2500000000 1404042436773 4000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25882919/62500000 : ℝ)^545 ≤ (15797217162971/50000000000000 : ℝ)^417 := by
    have hnat : (25882919 : ℕ)^545*50000000000000^417 ≤ 15797217162971^417*62500000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25882919 62500000 15797217162971 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311705293/10000000000 : ℝ), (1122140983/2500000000 : ℝ), (25882919/62500000 : ℝ)] ![(16652252371281/50000000000000 : ℝ), (1404042436773/4000000000000 : ℝ), (15797217162971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311705293/10000000000 : ℝ)|^545 ≤ (16652252371281/50000000000000 : ℝ)^417
        have hw : |(4311705293/10000000000 : ℝ)|=(4311705293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122140983/2500000000 : ℝ)|^545 ≤ (1404042436773/4000000000000 : ℝ)^417
        have hw : |(1122140983/2500000000 : ℝ)|=(1122140983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25882919/62500000 : ℝ)|^545 ≤ (15797217162971/50000000000000 : ℝ)^417
        have hw : |(25882919/62500000 : ℝ)|=(25882919/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (141/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (9239988204718073/100000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^4359 ≤ (9239988204718073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11279 : ℕ)^4359*100000000000000000000^1024 ≤ 9239988204718073^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 9239988204718073 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (9239988204718073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7371/50000 : ℝ) ^ (4359/1024 : ℝ) ≤ (577711520814969/2000000000000000000 : ℝ) := by
    have hpowers : (7371/50000 : ℝ)^4359 ≤ (577711520814969/2000000000000000000 : ℝ)^1024 := by
      have hnat : (7371 : ℕ)^4359*2000000000000000000^1024 ≤ 577711520814969^1024*50000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7371 50000 577711520814969 2000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7371/50000 : ℝ)) (X := (577711520814969/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009239988204718073/50000000000000000000 : ℝ) ≤ (1250054261752173/1250000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50009239988204718073/50000000000000000000 : ℝ)^1024 ≤ (1250054261752173/1250000000000000 : ℝ)^4359 := by
      have hnat : (50009239988204718073 : ℕ)^1024*1250000000000000^4359 ≤ 1250054261752173^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009239988204718073 50000000000000000000 1250054261752173 1250000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250054261752173/1250000000000000 : ℝ)) (X := (50009239988204718073/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038125564245466523/100000000000000000000 : ℝ) ≤ (10000895500920913/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (100038125564245466523/100000000000000000000 : ℝ)^1024 ≤ (10000895500920913/10000000000000000 : ℝ)^4359 := by
      have hnat : (100038125564245466523 : ℕ)^1024*10000000000000000^4359 ≤ 10000895500920913^4359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038125564245466523 100000000000000000000 10000895500920913 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000895500920913/10000000000000000 : ℝ)) (X := (100038125564245466523/100000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000577711520814969/1000000000000000000 : ℝ) ≤ (5000678453912221/5000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (1000577711520814969/1000000000000000000 : ℝ)^1024 ≤ (5000678453912221/5000000000000000 : ℝ)^4359 := by
      have hnat : (1000577711520814969 : ℕ)^1024*5000000000000000^4359 ≤ 5000678453912221^4359*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000577711520814969 1000000000000000000 5000678453912221 5000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000678453912221/5000000000000000 : ℝ)) (X := (1000577711520814969/1000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9239988204718073/100000000000000000000 : ℝ) ≤ ((3462109485065239361/3463000000000000000 : ℝ)+2*(461406903529/346300000000000 : ℝ)*(11279/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (3462109485065239361/3463000000000000000 : ℝ)+2*(461406903529/346300000000000 : ℝ)*(11279/100000 : ℝ)=(1250054261752173/1250000000000000 : ℝ) by norm_num, show 1+2*(9239988204718073/100000000000000000000 : ℝ)=(50009239988204718073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(577711520814969/2000000000000000000 : ℝ)+(9239988204718073/100000000000000000000 : ℝ) ≤ ((3462109485065239361/3463000000000000000 : ℝ)+(461406903529/346300000000000 : ℝ)*((7371/50000 : ℝ)+(11279/100000 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (3462109485065239361/3463000000000000000 : ℝ)+(461406903529/346300000000000 : ℝ)*((7371/50000 : ℝ)+(11279/100000 : ℝ))=(10000895500920913/10000000000000000 : ℝ) by norm_num, show 1+(577711520814969/2000000000000000000 : ℝ)+(9239988204718073/100000000000000000000 : ℝ)=(100038125564245466523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(577711520814969/2000000000000000000 : ℝ) ≤ ((3462109485065239361/3463000000000000000 : ℝ)+2*(461406903529/346300000000000 : ℝ)*(7371/50000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (3462109485065239361/3463000000000000000 : ℝ)+2*(461406903529/346300000000000 : ℝ)*(7371/50000 : ℝ)=(5000678453912221/5000000000000000 : ℝ) by norm_num, show 1+2*(577711520814969/2000000000000000000 : ℝ)=(1000577711520814969/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3462109485065239361/3463000000000000000 : ℝ)*(X 1 0+X 2 0)+(461406903529/346300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (3462109485065239361/3463000000000000000 : ℝ)) (alpha := (461406903529/346300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3462109485065239361/3463000000000000000 : ℝ)*(X 0 1+X 2 1)+(461406903529/346300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (3462109485065239361/3463000000000000000 : ℝ)) (alpha := (461406903529/346300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3462109485065239361/3463000000000000000 : ℝ)*(X 0 2+X 1 2)+(461406903529/346300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (3462109485065239361/3463000000000000000 : ℝ)) (alpha := (461406903529/346300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1994906553/10000000000 : ℝ)*X 0 0+(5409686523/10000000000 : ℝ)*X 0 1+(1311561963/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42783307/80000000 : ℝ)*X 1 0+(-2078136329/10000000000 : ℝ)*X 1 1+(5246247739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347913783/10000000000 : ℝ)*X 2 0+(5246247573/10000000000 : ℝ)*X 2 1+(-519534001/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311680351/10000000000 : ℝ)*X 0 0+(4140002819/10000000000 : ℝ)*X 0 1+(4489821809/10000000000 : ℝ)*X 0 2+(4311680351/10000000000 : ℝ)*X 1 0+(4140002819/10000000000 : ℝ)*X 1 1+(4489821809/10000000000 : ℝ)*X 1 2+(4311680351/10000000000 : ℝ)*X 2 0+(4140002819/10000000000 : ℝ)*X 2 1+(4489821809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398983659/2000000000 : ℝ)*X 0 0+(2623417749/5000000000 : ℝ)*X 0 1+(135227393/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21222191/40000000 : ℝ)*X 1 0+(-191528801/1000000000 : ℝ)*X 1 1+(5409095713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652773873/5000000000 : ℝ)*X 2 0+(2704547859/5000000000 : ℝ)*X 2 1+(-239411001/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311705293/10000000000 : ℝ)*X 0 0+(1122140983/2500000000 : ℝ)*X 0 1+(25882919/62500000 : ℝ)*X 0 2+(4311705293/10000000000 : ℝ)*X 1 0+(1122140983/2500000000 : ℝ)*X 1 1+(25882919/62500000 : ℝ)*X 1 2+(4311705293/10000000000 : ℝ)*X 2 0+(1122140983/2500000000 : ℝ)*X 2 1+(25882919/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2366716866333787318683/432875000000000000000000000 : ℝ) := by norm_num
    linear_combination (126742839/50000000000000 : ℝ)*(base19) + (631372281/100000000000000 : ℝ)*(base23) + (17206229/20000000000000 : ℝ)*(lower2) + (406321/500000000000 : ℝ)*(upper5) + (89771447709203/2000000000000 : ℝ)*(major0) + (89771447709203/2000000000000 : ℝ)*(major1) + (89771447709203/2000000000000 : ℝ)*(major2) + (1529626477578231/25000000000000 : ℝ)*(sp0) + (6118508810792497/100000000000000 : ℝ)*(sp1) + (3059258758591943/50000000000000 : ℝ)*(sp2) + (2858623146710517/100000000000000 : ℝ)*(sp3) + (12238243243/100000000000000 : ℝ)*(sp4) + (9084277993/100000000000000 : ℝ)*(sp5) + (1646702851/50000000000000 : ℝ)*(sp7) + (142931322005811/5000000000000 : ℝ)*(f.failure) + (6118518148556167/100000000000000 : ℝ)*(f.sum) + (1161801163111/1731500000000000000000000000 : ℝ)*base65 + (36005908390931283/6926000000000000000000000000000 : ℝ)*base67 + (74787106308443283/6926000000000000000000000000000 : ℝ)*base69 + (32464488304018717/6926000000000000000000000000000 : ℝ)*base72 + (7487854164449/1731500000000000000000000000 : ℝ)*base73 + (33313202747340717/6926000000000000000000000000000 : ℝ)*base76 + (50001401688343283/6926000000000000000000000000000 : ℝ)*base77 + (2195451732580717/6926000000000000000000000000000 : ℝ)*base80 + (4273322256563/3463000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6509311/500000000000000000000 : ℝ)*base89 + (6509311/500000000000000000000 : ℝ)*base91 + (6509311/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11533478227896700728561/1731500000000000000000000000 : ℝ) := by norm_num
    linear_combination (580710463/50000000000000 : ℝ)*(base19) + (155371437/12500000000000 : ℝ)*(base23) + (197126203/50000000000000 : ℝ)*(lower1) + (26926153/20000000000000 : ℝ)*(upper3) + (39561977/100000000000000 : ℝ)*(lower4) + (141052979/100000000000000 : ℝ)*(upper5) + (904228426476047/20000000000000 : ℝ)*(major0) + (904228426476047/20000000000000 : ℝ)*(major1) + (904228426476047/20000000000000 : ℝ)*(major2) + (1456412121/100000000000000 : ℝ)*(sp2) + (6162914985205069/100000000000000 : ℝ)*(sp4) + (3081456911892071/50000000000000 : ℝ)*(sp5) + (1540728071455363/25000000000000 : ℝ)*(sp6) + (719842264380717/25000000000000 : ℝ)*(sp7) + (719842264380717/25000000000000 : ℝ)*(f.failure) + (6162914985205069/100000000000000 : ℝ)*(f.sum) + (2437734738973/432875000000000000000000000 : ℝ)*base66 + (2047199011716835967/69260000000000000000000000000000 : ℝ)*base67 + (252281850282715967/69260000000000000000000000000000 : ℝ)*base69 + (5816356990216475967/69260000000000000000000000000000 : ℝ)*base71 + (518442485487/692600000000000000000000000 : ℝ)*base73 + (12760243909198444033/69260000000000000000000000000000 : ℝ)*base76 + (207007241711624033/69260000000000000000000000000000 : ℝ)*base78 + (194818907497984033/69260000000000000000000000000000 : ℝ)*base80 + (9627092388803/3463000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1645217/2500000000000000000000 : ℝ)*base89 + (1645217/2500000000000000000000 : ℝ)*base91 + (1645217/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1400_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1400_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1400_box_0 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-183211861/1000000000 : ℝ)*x 0 + (2693747059/5000000000 : ℝ)*x 1 + (673436771/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183211861/1000000000 : ℝ)^545 ≤ (10882130244957/100000000000000 : ℝ)^417 := by
    have hnat : (183211861 : ℕ)^545*100000000000000^417 ≤ 10882130244957^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183211861 1000000000 10882130244957 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693747059/5000000000 : ℝ)^545 ≤ (1113973364999/2500000000000 : ℝ)^417 := by
    have hnat : (2693747059 : ℕ)^545*2500000000000^417 ≤ 1113973364999^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693747059 5000000000 1113973364999 2500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673436771/1250000000 : ℝ)^545 ≤ (44558935140439/100000000000000 : ℝ)^417 := by
    have hnat : (673436771 : ℕ)^545*100000000000000^417 ≤ 44558935140439^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673436771 1250000000 44558935140439 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183211861/1000000000 : ℝ), (2693747059/5000000000 : ℝ), (673436771/1250000000 : ℝ)] ![(10882130244957/100000000000000 : ℝ), (1113973364999/2500000000000 : ℝ), (44558935140439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183211861/1000000000 : ℝ)|^545 ≤ (10882130244957/100000000000000 : ℝ)^417
        have hw : |(-183211861/1000000000 : ℝ)|=(183211861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693747059/5000000000 : ℝ)|^545 ≤ (1113973364999/2500000000000 : ℝ)^417
        have hw : |(2693747059/5000000000 : ℝ)|=(2693747059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673436771/1250000000 : ℝ)|^545 ≤ (44558935140439/100000000000000 : ℝ)^417
        have hw : |(673436771/1250000000 : ℝ)|=(673436771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_1 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (211433139/400000000 : ℝ)*x 0 + (-1971670217/10000000000 : ℝ)*x 1 + (5387494131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211433139/400000000 : ℝ)^545 ≤ (21731584744969/50000000000000 : ℝ)^417 := by
    have hnat : (211433139 : ℕ)^545*50000000000000^417 ≤ 21731584744969^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211433139 400000000 21731584744969 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971670217/10000000000 : ℝ)^545 ≤ (11977895751817/100000000000000 : ℝ)^417 := by
    have hnat : (1971670217 : ℕ)^545*100000000000000^417 ≤ 11977895751817^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971670217 10000000000 11977895751817 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387494131/10000000000 : ℝ)^545 ≤ (11139733685121/25000000000000 : ℝ)^417 := by
    have hnat : (5387494131 : ℕ)^545*25000000000000^417 ≤ 11139733685121^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387494131 10000000000 11139733685121 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211433139/400000000 : ℝ), (-1971670217/10000000000 : ℝ), (5387494131/10000000000 : ℝ)] ![(21731584744969/50000000000000 : ℝ), (11977895751817/100000000000000 : ℝ), (11139733685121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211433139/400000000 : ℝ)|^545 ≤ (21731584744969/50000000000000 : ℝ)^417
        have hw : |(211433139/400000000 : ℝ)|=(211433139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971670217/10000000000 : ℝ)|^545 ≤ (11977895751817/100000000000000 : ℝ)^417
        have hw : |(-1971670217/10000000000 : ℝ)|=(1971670217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387494131/10000000000 : ℝ)|^545 ≤ (11139733685121/25000000000000 : ℝ)^417
        have hw : |(5387494131/10000000000 : ℝ)|=(5387494131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_2 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5285828061/10000000000 : ℝ)*x 0 + (5387494593/10000000000 : ℝ)*x 1 + (-1971670149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285828061/10000000000 : ℝ)^545 ≤ (4346316504087/10000000000000 : ℝ)^417 := by
    have hnat : (5285828061 : ℕ)^545*10000000000000^417 ≤ 4346316504087^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285828061 10000000000 4346316504087 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387494593/10000000000 : ℝ)^545 ≤ (22279469867253/50000000000000 : ℝ)^417 := by
    have hnat : (5387494593 : ℕ)^545*50000000000000^417 ≤ 22279469867253^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387494593 10000000000 22279469867253 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971670149/10000000000 : ℝ)^545 ≤ (5988947605957/50000000000000 : ℝ)^417 := by
    have hnat : (1971670149 : ℕ)^545*50000000000000^417 ≤ 5988947605957^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971670149 10000000000 5988947605957 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285828061/10000000000 : ℝ), (5387494593/10000000000 : ℝ), (-1971670149/10000000000 : ℝ)] ![(4346316504087/10000000000000 : ℝ), (22279469867253/50000000000000 : ℝ), (5988947605957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285828061/10000000000 : ℝ)|^545 ≤ (4346316504087/10000000000000 : ℝ)^417
        have hw : |(5285828061/10000000000 : ℝ)|=(5285828061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387494593/10000000000 : ℝ)|^545 ≤ (22279469867253/50000000000000 : ℝ)^417
        have hw : |(5387494593/10000000000 : ℝ)|=(5387494593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971670149/10000000000 : ℝ)|^545 ≤ (5988947605957/50000000000000 : ℝ)^417
        have hw : |(-1971670149/10000000000 : ℝ)|=(1971670149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_3 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1114643511/2500000000 : ℝ)*x 0 + (212099989/500000000 : ℝ)*x 1 + (169680001/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114643511/2500000000 : ℝ)^545 ≤ (3479486326719/10000000000000 : ℝ)^417 := by
    have hnat : (1114643511 : ℕ)^545*10000000000000^417 ≤ 3479486326719^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114643511 2500000000 3479486326719 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212099989/500000000 : ℝ)^545 ≤ (2037660445793/6250000000000 : ℝ)^417 := by
    have hnat : (212099989 : ℕ)^545*6250000000000^417 ≤ 2037660445793^417*500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212099989 500000000 2037660445793 6250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169680001/400000000 : ℝ)^545 ≤ (16301284796833/50000000000000 : ℝ)^417 := by
    have hnat : (169680001 : ℕ)^545*50000000000000^417 ≤ 16301284796833^417*400000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169680001 400000000 16301284796833 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1114643511/2500000000 : ℝ), (212099989/500000000 : ℝ), (169680001/400000000 : ℝ)] ![(3479486326719/10000000000000 : ℝ), (2037660445793/6250000000000 : ℝ), (16301284796833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1114643511/2500000000 : ℝ)|^545 ≤ (3479486326719/10000000000000 : ℝ)^417
        have hw : |(1114643511/2500000000 : ℝ)|=(1114643511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212099989/500000000 : ℝ)|^545 ≤ (2037660445793/6250000000000 : ℝ)^417
        have hw : |(212099989/500000000 : ℝ)|=(212099989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169680001/400000000 : ℝ)|^545 ≤ (16301284796833/50000000000000 : ℝ)^417
        have hw : |(169680001/400000000 : ℝ)|=(169680001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_4 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160435523/10000000000 : ℝ)*x 0 + (2633032399/5000000000 : ℝ)*x 1 + (65825811/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160435523/10000000000 : ℝ)^545 ≤ (13498198556451/100000000000000 : ℝ)^417 := by
    have hnat : (2160435523 : ℕ)^545*100000000000000^417 ≤ 13498198556451^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160435523 10000000000 13498198556451 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633032399/5000000000 : ℝ)^545 ≤ (43250900274443/100000000000000 : ℝ)^417 := by
    have hnat : (2633032399 : ℕ)^545*100000000000000^417 ≤ 43250900274443^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633032399 5000000000 43250900274443 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65825811/125000000 : ℝ)^545 ≤ (43250901154647/100000000000000 : ℝ)^417 := by
    have hnat : (65825811 : ℕ)^545*100000000000000^417 ≤ 43250901154647^417*125000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65825811 125000000 43250901154647 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160435523/10000000000 : ℝ), (2633032399/5000000000 : ℝ), (65825811/125000000 : ℝ)] ![(13498198556451/100000000000000 : ℝ), (43250900274443/100000000000000 : ℝ), (43250901154647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160435523/10000000000 : ℝ)|^545 ≤ (13498198556451/100000000000000 : ℝ)^417
        have hw : |(-2160435523/10000000000 : ℝ)|=(2160435523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633032399/5000000000 : ℝ)|^545 ≤ (43250900274443/100000000000000 : ℝ)^417
        have hw : |(2633032399/5000000000 : ℝ)|=(2633032399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65825811/125000000 : ℝ)|^545 ≤ (43250901154647/100000000000000 : ℝ)^417
        have hw : |(65825811/125000000 : ℝ)|=(65825811/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_5 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1342727969/2500000000 : ℝ)*x 0 + (-252597993/1250000000 : ℝ)*x 1 + (526606467/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342727969/2500000000 : ℝ)^545 ≤ (5547471552673/12500000000000 : ℝ)^417 := by
    have hnat : (1342727969 : ℕ)^545*12500000000000^417 ≤ 5547471552673^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342727969 2500000000 5547471552673 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252597993/1250000000 : ℝ)^545 ≤ (19790925873/160000000000 : ℝ)^417 := by
    have hnat : (252597993 : ℕ)^545*160000000000^417 ≤ 19790925873^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252597993 1250000000 19790925873 160000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526606467/1000000000 : ℝ)^545 ≤ (43250898900467/100000000000000 : ℝ)^417 := by
    have hnat : (526606467 : ℕ)^545*100000000000000^417 ≤ 43250898900467^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526606467 1000000000 43250898900467 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342727969/2500000000 : ℝ), (-252597993/1250000000 : ℝ), (526606467/1000000000 : ℝ)] ![(5547471552673/12500000000000 : ℝ), (19790925873/160000000000 : ℝ), (43250898900467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342727969/2500000000 : ℝ)|^545 ≤ (5547471552673/12500000000000 : ℝ)^417
        have hw : |(1342727969/2500000000 : ℝ)|=(1342727969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252597993/1250000000 : ℝ)|^545 ≤ (19790925873/160000000000 : ℝ)^417
        have hw : |(-252597993/1250000000 : ℝ)|=(252597993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526606467/1000000000 : ℝ)|^545 ≤ (43250898900467/100000000000000 : ℝ)^417
        have hw : |(526606467/1000000000 : ℝ)|=(526606467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_6 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2685455901/5000000000 : ℝ)*x 0 + (5266064841/10000000000 : ℝ)*x 1 + (-404156763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685455901/5000000000 : ℝ)^545 ≤ (5547471452779/12500000000000 : ℝ)^417 := by
    have hnat : (2685455901 : ℕ)^545*12500000000000^417 ≤ 5547471452779^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685455901 5000000000 5547471452779 12500000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266064841/10000000000 : ℝ)^545 ≤ (21625450368007/50000000000000 : ℝ)^417 := by
    have hnat : (5266064841 : ℕ)^545*50000000000000^417 ≤ 21625450368007^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266064841 10000000000 21625450368007 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404156763/2000000000 : ℝ)^545 ≤ (12369327638633/100000000000000 : ℝ)^417 := by
    have hnat : (404156763 : ℕ)^545*100000000000000^417 ≤ 12369327638633^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404156763 2000000000 12369327638633 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685455901/5000000000 : ℝ), (5266064841/10000000000 : ℝ), (-404156763/2000000000 : ℝ)] ![(5547471452779/12500000000000 : ℝ), (21625450368007/50000000000000 : ℝ), (12369327638633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685455901/5000000000 : ℝ)|^545 ≤ (5547471452779/12500000000000 : ℝ)^417
        have hw : |(2685455901/5000000000 : ℝ)|=(2685455901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266064841/10000000000 : ℝ)|^545 ≤ (21625450368007/50000000000000 : ℝ)^417
        have hw : |(5266064841/10000000000 : ℝ)|=(5266064841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404156763/2000000000 : ℝ)|^545 ≤ (12369327638633/100000000000000 : ℝ)^417
        have hw : |(-404156763/2000000000 : ℝ)|=(404156763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_7 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4163778579/10000000000 : ℝ)*x 0 + (1097336469/2500000000 : ℝ)*x 1 + (877869181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163778579/10000000000 : ℝ)^545 ≤ (31819083436757/100000000000000 : ℝ)^417 := by
    have hnat : (4163778579 : ℕ)^545*100000000000000^417 ≤ 31819083436757^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163778579 10000000000 31819083436757 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097336469/2500000000 : ℝ)^545 ≤ (17045229063637/50000000000000 : ℝ)^417 := by
    have hnat : (1097336469 : ℕ)^545*50000000000000^417 ≤ 17045229063637^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097336469 2500000000 17045229063637 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877869181/2000000000 : ℝ)^545 ≤ (34090458421643/100000000000000 : ℝ)^417 := by
    have hnat : (877869181 : ℕ)^545*100000000000000^417 ≤ 34090458421643^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877869181 2000000000 34090458421643 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163778579/10000000000 : ℝ), (1097336469/2500000000 : ℝ), (877869181/2000000000 : ℝ)] ![(31819083436757/100000000000000 : ℝ), (17045229063637/50000000000000 : ℝ), (34090458421643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163778579/10000000000 : ℝ)|^545 ≤ (31819083436757/100000000000000 : ℝ)^417
        have hw : |(4163778579/10000000000 : ℝ)|=(4163778579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097336469/2500000000 : ℝ)|^545 ≤ (17045229063637/50000000000000 : ℝ)^417
        have hw : |(1097336469/2500000000 : ℝ)|=(1097336469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(877869181/2000000000 : ℝ)|^545 ≤ (34090458421643/100000000000000 : ℝ)^417
        have hw : |(877869181/2000000000 : ℝ)|=(877869181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_8 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-522836887/2500000000 : ℝ)*x 0 + (323887759/625000000 : ℝ)*x 1 + (540148529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522836887/2500000000 : ℝ)^545 ≤ (1293683449837/10000000000000 : ℝ)^417 := by
    have hnat : (522836887 : ℕ)^545*10000000000000^417 ≤ 1293683449837^417*2500000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522836887 2500000000 1293683449837 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323887759/625000000 : ℝ)^545 ≤ (42352932082601/100000000000000 : ℝ)^417 := by
    have hnat : (323887759 : ℕ)^545*100000000000000^417 ≤ 42352932082601^417*625000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323887759 625000000 42352932082601 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540148529/1000000000 : ℝ)^545 ≤ (1397194793857/3125000000000 : ℝ)^417 := by
    have hnat : (540148529 : ℕ)^545*3125000000000^417 ≤ 1397194793857^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540148529 1000000000 1397194793857 3125000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522836887/2500000000 : ℝ), (323887759/625000000 : ℝ), (540148529/1000000000 : ℝ)] ![(1293683449837/10000000000000 : ℝ), (42352932082601/100000000000000 : ℝ), (1397194793857/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522836887/2500000000 : ℝ)|^545 ≤ (1293683449837/10000000000000 : ℝ)^417
        have hw : |(-522836887/2500000000 : ℝ)|=(522836887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323887759/625000000 : ℝ)|^545 ≤ (42352932082601/100000000000000 : ℝ)^417
        have hw : |(323887759/625000000 : ℝ)|=(323887759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540148529/1000000000 : ℝ)|^545 ≤ (1397194793857/3125000000000 : ℝ)^417
        have hw : |(540148529/1000000000 : ℝ)|=(540148529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_9 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2638010253/5000000000 : ℝ)*x 0 + (-245735411/1250000000 : ℝ)*x 1 + (675185651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638010253/5000000000 : ℝ)^545 ≤ (43357797760061/100000000000000 : ℝ)^417 := by
    have hnat : (2638010253 : ℕ)^545*100000000000000^417 ≤ 43357797760061^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638010253 5000000000 43357797760061 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245735411/1250000000 : ℝ)^545 ≤ (1193196970713/10000000000000 : ℝ)^417 := by
    have hnat : (245735411 : ℕ)^545*10000000000000^417 ≤ 1193196970713^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245735411 1250000000 1193196970713 10000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675185651/1250000000 : ℝ)^545 ≤ (44710232516333/100000000000000 : ℝ)^417 := by
    have hnat : (675185651 : ℕ)^545*100000000000000^417 ≤ 44710232516333^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675185651 1250000000 44710232516333 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638010253/5000000000 : ℝ), (-245735411/1250000000 : ℝ), (675185651/1250000000 : ℝ)] ![(43357797760061/100000000000000 : ℝ), (1193196970713/10000000000000 : ℝ), (44710232516333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638010253/5000000000 : ℝ)|^545 ≤ (43357797760061/100000000000000 : ℝ)^417
        have hw : |(2638010253/5000000000 : ℝ)|=(2638010253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245735411/1250000000 : ℝ)|^545 ≤ (1193196970713/10000000000000 : ℝ)^417
        have hw : |(-245735411/1250000000 : ℝ)|=(245735411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675185651/1250000000 : ℝ)|^545 ≤ (44710232516333/100000000000000 : ℝ)^417
        have hw : |(675185651/1250000000 : ℝ)|=(675185651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_10 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5276020631/10000000000 : ℝ)*x 0 + (5401485217/10000000000 : ℝ)*x 1 + (-1965883107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276020631/10000000000 : ℝ)^545 ≤ (21678899551307/50000000000000 : ℝ)^417 := by
    have hnat : (5276020631 : ℕ)^545*50000000000000^417 ≤ 21678899551307^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276020631 10000000000 21678899551307 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401485217/10000000000 : ℝ)^545 ≤ (44710232613697/100000000000000 : ℝ)^417 := by
    have hnat : (5401485217 : ℕ)^545*100000000000000^417 ≤ 44710232613697^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401485217 10000000000 44710232613697 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965883107/10000000000 : ℝ)^545 ≤ (2982992067833/25000000000000 : ℝ)^417 := by
    have hnat : (1965883107 : ℕ)^545*25000000000000^417 ≤ 2982992067833^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965883107 10000000000 2982992067833 25000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276020631/10000000000 : ℝ), (5401485217/10000000000 : ℝ), (-1965883107/10000000000 : ℝ)] ![(21678899551307/50000000000000 : ℝ), (44710232613697/100000000000000 : ℝ), (2982992067833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276020631/10000000000 : ℝ)|^545 ≤ (21678899551307/50000000000000 : ℝ)^417
        have hw : |(5276020631/10000000000 : ℝ)|=(5276020631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401485217/10000000000 : ℝ)|^545 ≤ (44710232613697/100000000000000 : ℝ)^417
        have hw : |(5401485217/10000000000 : ℝ)|=(5401485217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965883107/10000000000 : ℝ)|^545 ≤ (2982992067833/25000000000000 : ℝ)^417
        have hw : |(-1965883107/10000000000 : ℝ)|=(1965883107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_11 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4491982359/10000000000 : ℝ)*x 0 + (4225008699/10000000000 : ℝ)*x 1 + (2112504191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4491982359/10000000000 : ℝ)^545 ≤ (17568001563323/50000000000000 : ℝ)^417 := by
    have hnat : (4491982359 : ℕ)^545*50000000000000^417 ≤ 17568001563323^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491982359 10000000000 17568001563323 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225008699/10000000000 : ℝ)^545 ≤ (6486400003511/20000000000000 : ℝ)^417 := by
    have hnat : (4225008699 : ℕ)^545*20000000000000^417 ≤ 6486400003511^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225008699 10000000000 6486400003511 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112504191/5000000000 : ℝ)^545 ≤ (32431996837271/100000000000000 : ℝ)^417 := by
    have hnat : (2112504191 : ℕ)^545*100000000000000^417 ≤ 32431996837271^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112504191 5000000000 32431996837271 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4491982359/10000000000 : ℝ), (4225008699/10000000000 : ℝ), (2112504191/5000000000 : ℝ)] ![(17568001563323/50000000000000 : ℝ), (6486400003511/20000000000000 : ℝ), (32431996837271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4491982359/10000000000 : ℝ)|^545 ≤ (17568001563323/50000000000000 : ℝ)^417
        have hw : |(4491982359/10000000000 : ℝ)|=(4491982359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225008699/10000000000 : ℝ)|^545 ≤ (6486400003511/20000000000000 : ℝ)^417
        have hw : |(4225008699/10000000000 : ℝ)|=(4225008699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112504191/5000000000 : ℝ)|^545 ≤ (32431996837271/100000000000000 : ℝ)^417
        have hw : |(2112504191/5000000000 : ℝ)|=(2112504191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_12 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901436493/10000000000 : ℝ)*x 0 + (5469273817/10000000000 : ℝ)*x 1 + (656869301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901436493/10000000000 : ℝ)^545 ≤ (22846663661/200000000000 : ℝ)^417 := by
    have hnat : (1901436493 : ℕ)^545*200000000000^417 ≤ 22846663661^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901436493 10000000000 22846663661 200000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469273817/10000000000 : ℝ)^545 ≤ (45444990317541/100000000000000 : ℝ)^417 := by
    have hnat : (5469273817 : ℕ)^545*100000000000000^417 ≤ 45444990317541^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469273817 10000000000 45444990317541 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656869301/1250000000 : ℝ)^545 ≤ (21565838920071/50000000000000 : ℝ)^417 := by
    have hnat : (656869301 : ℕ)^545*50000000000000^417 ≤ 21565838920071^417*1250000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656869301 1250000000 21565838920071 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901436493/10000000000 : ℝ), (5469273817/10000000000 : ℝ), (656869301/1250000000 : ℝ)] ![(22846663661/200000000000 : ℝ), (45444990317541/100000000000000 : ℝ), (21565838920071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901436493/10000000000 : ℝ)|^545 ≤ (22846663661/200000000000 : ℝ)^417
        have hw : |(-1901436493/10000000000 : ℝ)|=(1901436493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469273817/10000000000 : ℝ)|^545 ≤ (45444990317541/100000000000000 : ℝ)^417
        have hw : |(5469273817/10000000000 : ℝ)|=(5469273817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656869301/1250000000 : ℝ)|^545 ≤ (21565838920071/50000000000000 : ℝ)^417
        have hw : |(656869301/1250000000 : ℝ)|=(656869301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_13 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5378694279/10000000000 : ℝ)*x 0 + (-2025176657/10000000000 : ℝ)*x 1 + (5254954813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378694279/10000000000 : ℝ)^545 ≤ (2778989748453/6250000000000 : ℝ)^417 := by
    have hnat : (5378694279 : ℕ)^545*6250000000000^417 ≤ 2778989748453^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378694279 10000000000 2778989748453 6250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025176657/10000000000 : ℝ)^545 ≤ (155056022829/1250000000000 : ℝ)^417 := by
    have hnat : (2025176657 : ℕ)^545*1250000000000^417 ≤ 155056022829^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025176657 10000000000 155056022829 1250000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254954813/10000000000 : ℝ)^545 ≤ (43131682184673/100000000000000 : ℝ)^417 := by
    have hnat : (5254954813 : ℕ)^545*100000000000000^417 ≤ 43131682184673^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254954813 10000000000 43131682184673 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378694279/10000000000 : ℝ), (-2025176657/10000000000 : ℝ), (5254954813/10000000000 : ℝ)] ![(2778989748453/6250000000000 : ℝ), (155056022829/1250000000000 : ℝ), (43131682184673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378694279/10000000000 : ℝ)|^545 ≤ (2778989748453/6250000000000 : ℝ)^417
        have hw : |(5378694279/10000000000 : ℝ)|=(5378694279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025176657/10000000000 : ℝ)|^545 ≤ (155056022829/1250000000000 : ℝ)^417
        have hw : |(-2025176657/10000000000 : ℝ)|=(2025176657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254954813/10000000000 : ℝ)|^545 ≤ (43131682184673/100000000000000 : ℝ)^417
        have hw : |(5254954813/10000000000 : ℝ)|=(5254954813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_14 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5378695007/10000000000 : ℝ)*x 0 + (5254954593/10000000000 : ℝ)*x 1 + (-202517597/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378695007/10000000000 : ℝ)^545 ≤ (44463843840667/100000000000000 : ℝ)^417 := by
    have hnat : (5378695007 : ℕ)^545*100000000000000^417 ≤ 44463843840667^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378695007 10000000000 44463843840667 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254954593/10000000000 : ℝ)^545 ≤ (43131679824681/100000000000000 : ℝ)^417 := by
    have hnat : (5254954593 : ℕ)^545*100000000000000^417 ≤ 43131679824681^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254954593 10000000000 43131679824681 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202517597/1000000000 : ℝ)^545 ≤ (6202238163349/50000000000000 : ℝ)^417 := by
    have hnat : (202517597 : ℕ)^545*50000000000000^417 ≤ 6202238163349^417*1000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202517597 1000000000 6202238163349 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378695007/10000000000 : ℝ), (5254954593/10000000000 : ℝ), (-202517597/1000000000 : ℝ)] ![(44463843840667/100000000000000 : ℝ), (43131679824681/100000000000000 : ℝ), (6202238163349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378695007/10000000000 : ℝ)|^545 ≤ (44463843840667/100000000000000 : ℝ)^417
        have hw : |(5378695007/10000000000 : ℝ)|=(5378695007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254954593/10000000000 : ℝ)|^545 ≤ (43131679824681/100000000000000 : ℝ)^417
        have hw : |(5254954593/10000000000 : ℝ)|=(5254954593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202517597/1000000000 : ℝ)|^545 ≤ (6202238163349/50000000000000 : ℝ)^417
        have hw : |(-202517597/1000000000 : ℝ)|=(202517597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1400_box_15 (p : ℝ) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2068178507/5000000000 : ℝ)*x 0 + (880563269/2000000000 : ℝ)*x 1 + (4402816517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068178507/5000000000 : ℝ)^545 ≤ (31545485471671/100000000000000 : ℝ)^417 := by
    have hnat : (2068178507 : ℕ)^545*100000000000000^417 ≤ 31545485471671^417*5000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068178507 5000000000 31545485471671 100000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880563269/2000000000 : ℝ)^545 ≤ (17113628191531/50000000000000 : ℝ)^417 := by
    have hnat : (880563269 : ℕ)^545*50000000000000^417 ≤ 17113628191531^417*2000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880563269 2000000000 17113628191531 50000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402816517/10000000000 : ℝ)^545 ≤ (6845451626123/20000000000000 : ℝ)^417 := by
    have hnat : (4402816517 : ℕ)^545*20000000000000^417 ≤ 6845451626123^417*10000000000^545 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402816517 10000000000 6845451626123 20000000000000 545 417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (545/128 : ℝ)) 545 417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2068178507/5000000000 : ℝ), (880563269/2000000000 : ℝ), (4402816517/10000000000 : ℝ)] ![(31545485471671/100000000000000 : ℝ), (17113628191531/50000000000000 : ℝ), (6845451626123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2068178507/5000000000 : ℝ)|^545 ≤ (31545485471671/100000000000000 : ℝ)^417
        have hw : |(2068178507/5000000000 : ℝ)|=(2068178507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880563269/2000000000 : ℝ)|^545 ≤ (17113628191531/50000000000000 : ℝ)^417
        have hw : |(880563269/2000000000 : ℝ)|=(880563269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4402816517/10000000000 : ℝ)|^545 ≤ (6845451626123/20000000000000 : ℝ)^417
        have hw : |(4402816517/10000000000 : ℝ)|=(4402816517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1400_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h) :
    -(62883/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11811/20000 : ℝ) ∧ (80287/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (3383/4000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (141/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (141/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (141/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (141/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (141/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (141/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (141/1250 : ℝ) ^ (4359/1024 : ℝ) ≤ (9243475995567621/100000000000000000000 : ℝ) := by
    have hpowers : (141/1250 : ℝ)^4359 ≤ (9243475995567621/100000000000000000000 : ℝ)^1024 := by
      have hnat : (141 : ℕ)^4359*100000000000000000000^1024 ≤ 9243475995567621^1024*1250^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1250 9243475995567621 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1250 : ℝ)) (X := (9243475995567621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14741/100000 : ℝ) ^ (4359/1024 : ℝ) ≤ (28877236088473973/100000000000000000000 : ℝ) := by
    have hpowers : (14741/100000 : ℝ)^4359 ≤ (28877236088473973/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14741 : ℕ)^4359*100000000000000000000^1024 ≤ 28877236088473973^1024*100000^4359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14741 100000 28877236088473973 100000000000000000000 4359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14741/100000 : ℝ)) (X := (28877236088473973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009243475995567621/50000000000000000000 : ℝ) ≤ (400017370314479/400000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50009243475995567621/50000000000000000000 : ℝ)^1024 ≤ (400017370314479/400000000000000 : ℝ)^4359 := by
      have hnat : (50009243475995567621 : ℕ)^1024*400000000000000^4359 ≤ 400017370314479^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009243475995567621 50000000000000000000 400017370314479 400000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400017370314479/400000000000000 : ℝ)) (X := (50009243475995567621/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019060356042020797/50000000000000000000 : ℝ) ≤ (1250111923371123/1250000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50019060356042020797/50000000000000000000 : ℝ)^1024 ≤ (1250111923371123/1250000000000000 : ℝ)^4359 := by
      have hnat : (50019060356042020797 : ℕ)^1024*1250000000000000^4359 ≤ 1250111923371123^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019060356042020797 50000000000000000000 1250111923371123 1250000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250111923371123/1250000000000000 : ℝ)) (X := (50019060356042020797/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028877236088473973/50000000000000000000 : ℝ) ≤ (10001356516075993/10000000000000000 : ℝ) ^ (4359/1024 : ℝ) := by
    have hpowers : (50028877236088473973/50000000000000000000 : ℝ)^1024 ≤ (10001356516075993/10000000000000000 : ℝ)^4359 := by
      have hnat : (50028877236088473973 : ℕ)^1024*10000000000000000^4359 ≤ 10001356516075993^4359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028877236088473973 50000000000000000000 10001356516075993 10000000000000000 1024 4359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001356516075993/10000000000000000 : ℝ)) (X := (50028877236088473973/50000000000000000000 : ℝ)) (by norm_num) 4359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9243475995567621/100000000000000000000 : ℝ) ≤ ((6920219978761234487/6922000000000000000 : ℝ)+2*(461129107009/346100000000000 : ℝ)*(141/1250 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (6920219978761234487/6922000000000000000 : ℝ)+2*(461129107009/346100000000000 : ℝ)*(141/1250 : ℝ)=(400017370314479/400000000000000 : ℝ) by norm_num, show 1+2*(9243475995567621/100000000000000000000 : ℝ)=(50009243475995567621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28877236088473973/100000000000000000000 : ℝ)+(9243475995567621/100000000000000000000 : ℝ) ≤ ((6920219978761234487/6922000000000000000 : ℝ)+(461129107009/346100000000000 : ℝ)*((14741/100000 : ℝ)+(141/1250 : ℝ)))^(4359/1024 : ℝ) := by
    rw [show (6920219978761234487/6922000000000000000 : ℝ)+(461129107009/346100000000000 : ℝ)*((14741/100000 : ℝ)+(141/1250 : ℝ))=(1250111923371123/1250000000000000 : ℝ) by norm_num, show 1+(28877236088473973/100000000000000000000 : ℝ)+(9243475995567621/100000000000000000000 : ℝ)=(50019060356042020797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28877236088473973/100000000000000000000 : ℝ) ≤ ((6920219978761234487/6922000000000000000 : ℝ)+2*(461129107009/346100000000000 : ℝ)*(14741/100000 : ℝ))^(4359/1024 : ℝ) := by
    rw [show (6920219978761234487/6922000000000000000 : ℝ)+2*(461129107009/346100000000000 : ℝ)*(14741/100000 : ℝ)=(10001356516075993/10000000000000000 : ℝ) by norm_num, show 1+2*(28877236088473973/100000000000000000000 : ℝ)=(50028877236088473973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6920219978761234487/6922000000000000000 : ℝ)*(X 1 0+X 2 0)+(461129107009/346100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (6920219978761234487/6922000000000000000 : ℝ)) (alpha := (461129107009/346100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6920219978761234487/6922000000000000000 : ℝ)*(X 0 1+X 2 1)+(461129107009/346100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (6920219978761234487/6922000000000000000 : ℝ)) (alpha := (461129107009/346100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6920219978761234487/6922000000000000000 : ℝ)*(X 0 2+X 1 2)+(461129107009/346100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4359/1024 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (6920219978761234487/6922000000000000000 : ℝ)) (alpha := (461129107009/346100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-183211861/1000000000 : ℝ)*X 0 0+(2693747059/5000000000 : ℝ)*X 0 1+(673436771/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((211433139/400000000 : ℝ)*X 1 0+(-1971670217/10000000000 : ℝ)*X 1 1+(5387494131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285828061/10000000000 : ℝ)*X 2 0+(5387494593/10000000000 : ℝ)*X 2 1+(-1971670149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1114643511/2500000000 : ℝ)*X 0 0+(212099989/500000000 : ℝ)*X 0 1+(169680001/400000000 : ℝ)*X 0 2+(1114643511/2500000000 : ℝ)*X 1 0+(212099989/500000000 : ℝ)*X 1 1+(169680001/400000000 : ℝ)*X 1 2+(1114643511/2500000000 : ℝ)*X 2 0+(212099989/500000000 : ℝ)*X 2 1+(169680001/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2160435523/10000000000 : ℝ)*X 0 0+(2633032399/5000000000 : ℝ)*X 0 1+(65825811/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342727969/2500000000 : ℝ)*X 1 0+(-252597993/1250000000 : ℝ)*X 1 1+(526606467/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685455901/5000000000 : ℝ)*X 2 0+(5266064841/10000000000 : ℝ)*X 2 1+(-404156763/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4163778579/10000000000 : ℝ)*X 0 0+(1097336469/2500000000 : ℝ)*X 0 1+(877869181/2000000000 : ℝ)*X 0 2+(4163778579/10000000000 : ℝ)*X 1 0+(1097336469/2500000000 : ℝ)*X 1 1+(877869181/2000000000 : ℝ)*X 1 2+(4163778579/10000000000 : ℝ)*X 2 0+(1097336469/2500000000 : ℝ)*X 2 1+(877869181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-522836887/2500000000 : ℝ)*X 0 0+(323887759/625000000 : ℝ)*X 0 1+(540148529/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638010253/5000000000 : ℝ)*X 1 0+(-245735411/1250000000 : ℝ)*X 1 1+(675185651/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276020631/10000000000 : ℝ)*X 2 0+(5401485217/10000000000 : ℝ)*X 2 1+(-1965883107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4491982359/10000000000 : ℝ)*X 0 0+(4225008699/10000000000 : ℝ)*X 0 1+(2112504191/5000000000 : ℝ)*X 0 2+(4491982359/10000000000 : ℝ)*X 1 0+(4225008699/10000000000 : ℝ)*X 1 1+(2112504191/5000000000 : ℝ)*X 1 2+(4491982359/10000000000 : ℝ)*X 2 0+(4225008699/10000000000 : ℝ)*X 2 1+(2112504191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1901436493/10000000000 : ℝ)*X 0 0+(5469273817/10000000000 : ℝ)*X 0 1+(656869301/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378694279/10000000000 : ℝ)*X 1 0+(-2025176657/10000000000 : ℝ)*X 1 1+(5254954813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378695007/10000000000 : ℝ)*X 2 0+(5254954593/10000000000 : ℝ)*X 2 1+(-202517597/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2068178507/5000000000 : ℝ)*X 0 0+(880563269/2000000000 : ℝ)*X 0 1+(4402816517/10000000000 : ℝ)*X 0 2+(2068178507/5000000000 : ℝ)*X 1 0+(880563269/2000000000 : ℝ)*X 1 1+(4402816517/10000000000 : ℝ)*X 1 2+(2068178507/5000000000 : ℝ)*X 2 0+(880563269/2000000000 : ℝ)*X 2 1+(4402816517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1400_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62883/100000 : ℝ) ≤ (-27203484548193405076031580874791/43262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18749017/100000000000000 : ℝ)*(lower2) + (5908877/20000000000000 : ℝ)*(lower3) + (280583/50000000000000 : ℝ)*(upper5) + (746266927710031/25000000000000 : ℝ)*(major0) + (746266927710031/25000000000000 : ℝ)*(major1) + (746266927710031/25000000000000 : ℝ)*(major2) + (144550507/3125000000000 : ℝ)*(sp1) + (38988511/20000000000000 : ℝ)*(sp3) + (2045001147104829/50000000000000 : ℝ)*(sp4) + (1022499456988713/25000000000000 : ℝ)*(sp5) + (2044995021939091/50000000000000 : ℝ)*(sp6) + (950546396040377/50000000000000 : ℝ)*(sp7) + (159361417/100000000000000 : ℝ)*(sp12) + (12409692893/100000000000000 : ℝ)*(sp14) + (1901092987023309/100000000000000 : ℝ)*(f.failure) + (1022500613392769/25000000000000 : ℝ)*(f.sum) + (13645134744461/17305000000000000000000000000 : ℝ)*base65 + (1320306622748769097/173050000000000000000000000000000 : ℝ)*base67 + (1339166088674569097/173050000000000000000000000000000 : ℝ)*base69 + (445870327582280903/173050000000000000000000000000000 : ℝ)*base72 + (707696664603/2163125000000000000000000000 : ℝ)*base74 + (395909819640169097/173050000000000000000000000000000 : ℝ)*base75 + (1821640428895569097/173050000000000000000000000000000 : ℝ)*base77 + (862854340332869097/173050000000000000000000000000000 : ℝ)*base79 + (8118177220909/17305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (31239809/10000000000000000000000 : ℝ)*base89 + (31239809/10000000000000000000000 : ℝ)*base91 + (31239809/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11811/20000 : ℝ) ≤ (2554983714114162933201171454839/4326250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3299209/100000000000000 : ℝ)*(lower1) + (74515769/100000000000000 : ℝ)*(upper2) + (16512199/100000000000000 : ℝ)*(upper5) + (38196252452817/1250000000000 : ℝ)*(major0) + (38196252452817/1250000000000 : ℝ)*(major1) + (38196252452817/1250000000000 : ℝ)*(major2) + (20728175710237/500000000000 : ℝ)*(sp0) + (1036409104721863/25000000000000 : ℝ)*(sp1) + (2072812502501979/50000000000000 : ℝ)*(sp2) + (1946074286075323/100000000000000 : ℝ)*(sp3) + (1543488259/100000000000000 : ℝ)*(sp5) + (12957371753/100000000000000 : ℝ)*(sp6) + (2244247279/100000000000000 : ℝ)*(sp7) + (2820328311/100000000000000 : ℝ)*(sp12) + (973038265161301/50000000000000 : ℝ)*(f.failure) + (129551186324241/3125000000000 : ℝ)*(f.sum) + (6110253531791/1730500000000000000000000000 : ℝ)*base66 + (88115956353032379/8652500000000000000000000000000 : ℝ)*base67 + (105321391801914879/8652500000000000000000000000000 : ℝ)*base69 + (66513383281867379/8652500000000000000000000000000 : ℝ)*base71 + (1364756839111/865250000000000000000000000 : ℝ)*base73 + (144231289280679879/8652500000000000000000000000000 : ℝ)*base75 + (20048292270967379/8652500000000000000000000000000 : ℝ)*base77 + (60124175038332379/8652500000000000000000000000000 : ℝ)*base79 + (1729509694267/692200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6229801/5000000000000000000000 : ℝ)*base89 + (6229801/5000000000000000000000 : ℝ)*base91 + (6229801/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80287/100000 : ℝ) ≤ (34735280953623872614584035709789/43262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62783679/100000000000000 : ℝ)*(upper0) + (3127353/4000000000000 : ℝ)*(upper1) + (107852637/100000000000000 : ℝ)*(upper4) + (420642087073917/12500000000000 : ℝ)*(major0) + (420642087073917/12500000000000 : ℝ)*(major1) + (420642087073917/12500000000000 : ℝ)*(major2) + (69472419983/100000000000000 : ℝ)*(sp1) + (30330684577/25000000000000 : ℝ)*(sp2) + (32146328611/100000000000000 : ℝ)*(sp3) + (2082793659/50000000000000 : ℝ)*(sp4) + (4560359413410939/100000000000000 : ℝ)*(sp8) + (2280147053289137/50000000000000 : ℝ)*(sp9) + (91204845125199/2000000000000 : ℝ)*(sp10) + (6697232729497/312500000000 : ℝ)*(sp11) + (2143146619767651/100000000000000 : ℝ)*(f.failure) + (2280181789499129/50000000000000 : ℝ)*(f.sum) + (8396110768083/8652500000000000000000000000 : ℝ)*base66 + (1884515466805635579/86525000000000000000000000000000 : ℝ)*base67 + (2263525234548510579/86525000000000000000000000000000 : ℝ)*base69 + (1389463259628810579/86525000000000000000000000000000 : ℝ)*base71 + (573011671473339/17305000000000000000000000000 : ℝ)*base73 + (2120065779560635579/86525000000000000000000000000000 : ℝ)*base75 + (1002991848093585579/86525000000000000000000000000000 : ℝ)*base77 + (5141111851274285579/86525000000000000000000000000000 : ℝ)*base79 + (4275041830941/17305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (71688849/10000000000000000000000 : ℝ)*base90 + (71688849/10000000000000000000000 : ℝ)*base92 + (71688849/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-3383/4000 : ℝ) ≤ (-29270650321621649647548206478561/34610000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168797809/100000000000000 : ℝ)*(lower1) + (407671853/100000000000000 : ℝ)*(lower2) + (75315937/50000000000000 : ℝ)*(upper5) + (340227514549101/10000000000000 : ℝ)*(major0) + (340227514549101/10000000000000 : ℝ)*(major1) + (340227514549101/10000000000000 : ℝ)*(major2) + (3563603747/20000000000000 : ℝ)*(sp0) + (97205002841/50000000000000 : ℝ)*(sp5) + (107033606087/100000000000000 : ℝ)*(sp6) + (22090165769/20000000000000 : ℝ)*(sp7) + (583240564352869/12500000000000 : ℝ)*(sp12) + (2332873961418003/50000000000000 : ℝ)*(sp13) + (4665835299235601/100000000000000 : ℝ)*(sp14) + (541672111182493/25000000000000 : ℝ)*(sp15) + (1083399447779409/50000000000000 : ℝ)*(f.failure) + (583242791605211/12500000000000 : ℝ)*(f.sum) + (41125153356221/3461000000000000000000000000 : ℝ)*base65 + (313580042311946187/69220000000000000000000000000000 : ℝ)*base67 + (36087232737326187/69220000000000000000000000000000 : ℝ)*base69 + (115244080219953813/69220000000000000000000000000000 : ℝ)*base72 + (589913088213/216312500000000000000000000 : ℝ)*base73 + (330989218896486187/69220000000000000000000000000000 : ℝ)*base75 + (232502336247453813/69220000000000000000000000000000 : ℝ)*base78 + (170446646247826187/69220000000000000000000000000000 : ℝ)*base79 + (4883168199101/865250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (79845909/5000000000000000000000 : ℝ)*base89 + (79845909/5000000000000000000000 : ℝ)*base91 + (79845909/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1400_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62883/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11811/20000 : ℝ) else (80287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3383/4000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1400_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1400_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62883/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11811/20000 : ℝ) else (80287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3383/4000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1400_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1400_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1400_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4359/1024 : ℝ) ≤ p) (hpb : p ≤ (545/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157018501/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62883/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11811/20000 : ℝ) else (80287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3383/4000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1400_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
