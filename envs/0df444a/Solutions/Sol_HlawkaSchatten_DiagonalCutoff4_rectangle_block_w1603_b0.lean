-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1603_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:14.03244+00:00
-- url     : https://prove2.me/submissions/2e5674dc-6b14-4f00-9e0d-bcd1fbf03252

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
theorem support_rectangle_w1603_s0_0 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-157883963/1000000000 : ℝ)*x 0 + (5846673329/10000000000 : ℝ)*x 1 + (977545051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157883963/1000000000 : ℝ)^4731 ≤ (9481817712127/100000000000000 : ℝ)^3707 := by
    have hnat : (157883963 : ℕ)^4731*100000000000000^3707 ≤ 9481817712127^3707*1000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157883963 1000000000 9481817712127 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5846673329/10000000000 : ℝ)^4731 ≤ (1260262738937/2500000000000 : ℝ)^3707 := by
    have hnat : (5846673329 : ℕ)^4731*2500000000000^3707 ≤ 1260262738937^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5846673329 10000000000 1260262738937 2500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977545051/2000000000 : ℝ)^4731 ≤ (8021534543623/20000000000000 : ℝ)^3707 := by
    have hnat : (977545051 : ℕ)^4731*20000000000000^3707 ≤ 8021534543623^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977545051 2000000000 8021534543623 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-157883963/1000000000 : ℝ), (5846673329/10000000000 : ℝ), (977545051/2000000000 : ℝ)] ![(9481817712127/100000000000000 : ℝ), (1260262738937/2500000000000 : ℝ), (8021534543623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-157883963/1000000000 : ℝ)|^4731 ≤ (9481817712127/100000000000000 : ℝ)^3707
        have hw : |(-157883963/1000000000 : ℝ)|=(157883963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5846673329/10000000000 : ℝ)|^4731 ≤ (1260262738937/2500000000000 : ℝ)^3707
        have hw : |(5846673329/10000000000 : ℝ)|=(5846673329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(977545051/2000000000 : ℝ)|^4731 ≤ (8021534543623/20000000000000 : ℝ)^3707
        have hw : |(977545051/2000000000 : ℝ)|=(977545051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_1 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2728306123/5000000000 : ℝ)*x 0 + (-2110622469/10000000000 : ℝ)*x 1 + (4887725107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2728306123/5000000000 : ℝ)^4731 ≤ (23079280822349/50000000000000 : ℝ)^3707 := by
    have hnat : (2728306123 : ℕ)^4731*50000000000000^3707 ≤ 23079280822349^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728306123 5000000000 23079280822349 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110622469/10000000000 : ℝ)^4731 ≤ (13733767174309/100000000000000 : ℝ)^3707 := by
    have hnat : (2110622469 : ℕ)^4731*100000000000000^3707 ≤ 13733767174309^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110622469 10000000000 13733767174309 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4887725107/10000000000 : ℝ)^4731 ≤ (20053835584091/50000000000000 : ℝ)^3707 := by
    have hnat : (4887725107 : ℕ)^4731*50000000000000^3707 ≤ 20053835584091^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4887725107 10000000000 20053835584091 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2728306123/5000000000 : ℝ), (-2110622469/10000000000 : ℝ), (4887725107/10000000000 : ℝ)] ![(23079280822349/50000000000000 : ℝ), (13733767174309/100000000000000 : ℝ), (20053835584091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2728306123/5000000000 : ℝ)|^4731 ≤ (23079280822349/50000000000000 : ℝ)^3707
        have hw : |(2728306123/5000000000 : ℝ)|=(2728306123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110622469/10000000000 : ℝ)|^4731 ≤ (13733767174309/100000000000000 : ℝ)^3707
        have hw : |(-2110622469/10000000000 : ℝ)|=(2110622469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4887725107/10000000000 : ℝ)|^4731 ≤ (20053835584091/50000000000000 : ℝ)^3707
        have hw : |(4887725107/10000000000 : ℝ)|=(4887725107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_2 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1364153029/2500000000 : ℝ)*x 0 + (122193129/250000000 : ℝ)*x 1 + (-2110622571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1364153029/2500000000 : ℝ)^4731 ≤ (46158560241229/100000000000000 : ℝ)^3707 := by
    have hnat : (1364153029 : ℕ)^4731*100000000000000^3707 ≤ 46158560241229^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364153029 2500000000 46158560241229 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122193129/250000000 : ℝ)^4731 ≤ (20053835861613/50000000000000 : ℝ)^3707 := by
    have hnat : (122193129 : ℕ)^4731*50000000000000^3707 ≤ 20053835861613^3707*250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122193129 250000000 20053835861613 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110622571/10000000000 : ℝ)^4731 ≤ (171672100267/1250000000000 : ℝ)^3707 := by
    have hnat : (2110622571 : ℕ)^4731*1250000000000^3707 ≤ 171672100267^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110622571 10000000000 171672100267 1250000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1364153029/2500000000 : ℝ), (122193129/250000000 : ℝ), (-2110622571/10000000000 : ℝ)] ![(46158560241229/100000000000000 : ℝ), (20053835861613/50000000000000 : ℝ), (171672100267/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1364153029/2500000000 : ℝ)|^4731 ≤ (46158560241229/100000000000000 : ℝ)^3707
        have hw : |(1364153029/2500000000 : ℝ)|=(1364153029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122193129/250000000 : ℝ)|^4731 ≤ (20053835861613/50000000000000 : ℝ)^3707
        have hw : |(122193129/250000000 : ℝ)|=(122193129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110622571/10000000000 : ℝ)|^4731 ≤ (171672100267/1250000000000 : ℝ)^3707
        have hw : |(-2110622571/10000000000 : ℝ)|=(2110622571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_3 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4113230943/10000000000 : ℝ)*x 0 + (384151089/1250000000 : ℝ)*x 1 + (5407966657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4113230943/10000000000 : ℝ)^4731 ≤ (2011348407443/6250000000000 : ℝ)^3707 := by
    have hnat : (4113230943 : ℕ)^4731*6250000000000^3707 ≤ 2011348407443^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113230943 10000000000 2011348407443 6250000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384151089/1250000000 : ℝ)^4731 ≤ (2218438950877/10000000000000 : ℝ)^3707 := by
    have hnat : (384151089 : ℕ)^4731*10000000000000^3707 ≤ 2218438950877^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384151089 1250000000 2218438950877 10000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407966657/10000000000 : ℝ)^4731 ≤ (45634035953133/100000000000000 : ℝ)^3707 := by
    have hnat : (5407966657 : ℕ)^4731*100000000000000^3707 ≤ 45634035953133^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407966657 10000000000 45634035953133 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4113230943/10000000000 : ℝ), (384151089/1250000000 : ℝ), (5407966657/10000000000 : ℝ)] ![(2011348407443/6250000000000 : ℝ), (2218438950877/10000000000000 : ℝ), (45634035953133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4113230943/10000000000 : ℝ)|^4731 ≤ (2011348407443/6250000000000 : ℝ)^3707
        have hw : |(4113230943/10000000000 : ℝ)|=(4113230943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(384151089/1250000000 : ℝ)|^4731 ≤ (2218438950877/10000000000000 : ℝ)^3707
        have hw : |(384151089/1250000000 : ℝ)|=(384151089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407966657/10000000000 : ℝ)|^4731 ≤ (45634035953133/100000000000000 : ℝ)^3707
        have hw : |(5407966657/10000000000 : ℝ)|=(5407966657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_4 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-790864761/5000000000 : ℝ)*x 0 + (4912077357/10000000000 : ℝ)*x 1 + (1455363151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (790864761/5000000000 : ℝ)^4731 ≤ (9503972892413/100000000000000 : ℝ)^3707 := by
    have hnat : (790864761 : ℕ)^4731*100000000000000^3707 ≤ 9503972892413^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790864761 5000000000 9503972892413 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4912077357/10000000000 : ℝ)^4731 ≤ (40362875783989/100000000000000 : ℝ)^3707 := by
    have hnat : (4912077357 : ℕ)^4731*100000000000000^3707 ≤ 40362875783989^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4912077357 10000000000 40362875783989 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455363151/2500000000 : ℝ)^4731 ≤ (50133151306599/100000000000000 : ℝ)^3707 := by
    have hnat : (1455363151 : ℕ)^4731*100000000000000^3707 ≤ 50133151306599^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455363151 2500000000 50133151306599 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-790864761/5000000000 : ℝ), (4912077357/10000000000 : ℝ), (1455363151/2500000000 : ℝ)] ![(9503972892413/100000000000000 : ℝ), (40362875783989/100000000000000 : ℝ), (50133151306599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-790864761/5000000000 : ℝ)|^4731 ≤ (9503972892413/100000000000000 : ℝ)^3707
        have hw : |(-790864761/5000000000 : ℝ)|=(790864761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4912077357/10000000000 : ℝ)|^4731 ≤ (40362875783989/100000000000000 : ℝ)^3707
        have hw : |(4912077357/10000000000 : ℝ)|=(4912077357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1455363151/2500000000 : ℝ)|^4731 ≤ (50133151306599/100000000000000 : ℝ)^3707
        have hw : |(1455363151/2500000000 : ℝ)|=(1455363151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_5 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324668537/625000000 : ℝ)*x 0 + (-1176894357/10000000000 : ℝ)*x 1 + (582145291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324668537/625000000 : ℝ)^4731 ≤ (5418738700173/12500000000000 : ℝ)^3707 := by
    have hnat : (324668537 : ℕ)^4731*12500000000000^3707 ≤ 5418738700173^3707*625000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324668537 625000000 5418738700173 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1176894357/10000000000 : ℝ)^4731 ≤ (6516935711809/100000000000000 : ℝ)^3707 := by
    have hnat : (1176894357 : ℕ)^4731*100000000000000^3707 ≤ 6516935711809^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176894357 10000000000 6516935711809 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582145291/1000000000 : ℝ)^4731 ≤ (50133154669743/100000000000000 : ℝ)^3707 := by
    have hnat : (582145291 : ℕ)^4731*100000000000000^3707 ≤ 50133154669743^3707*1000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582145291 1000000000 50133154669743 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324668537/625000000 : ℝ), (-1176894357/10000000000 : ℝ), (582145291/1000000000 : ℝ)] ![(5418738700173/12500000000000 : ℝ), (6516935711809/100000000000000 : ℝ), (50133154669743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324668537/625000000 : ℝ)|^4731 ≤ (5418738700173/12500000000000 : ℝ)^3707
        have hw : |(324668537/625000000 : ℝ)|=(324668537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1176894357/10000000000 : ℝ)|^4731 ≤ (6516935711809/100000000000000 : ℝ)^3707
        have hw : |(-1176894357/10000000000 : ℝ)|=(1176894357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(582145291/1000000000 : ℝ)|^4731 ≤ (50133154669743/100000000000000 : ℝ)^3707
        have hw : |(582145291/1000000000 : ℝ)|=(582145291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_6 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194696693/10000000000 : ℝ)*x 0 + (46571621/80000000 : ℝ)*x 1 + (-147111831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194696693/10000000000 : ℝ)^4731 ≤ (677342354329/1562500000000 : ℝ)^3707 := by
    have hnat : (5194696693 : ℕ)^4731*1562500000000^3707 ≤ 677342354329^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194696693 10000000000 677342354329 1562500000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46571621/80000000 : ℝ)^4731 ≤ (50133151537403/100000000000000 : ℝ)^3707 := by
    have hnat : (46571621 : ℕ)^4731*100000000000000^3707 ≤ 50133151537403^3707*80000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46571621 80000000 50133151537403 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147111831/1250000000 : ℝ)^4731 ≤ (814617221039/12500000000000 : ℝ)^3707 := by
    have hnat : (147111831 : ℕ)^4731*12500000000000^3707 ≤ 814617221039^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147111831 1250000000 814617221039 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194696693/10000000000 : ℝ), (46571621/80000000 : ℝ), (-147111831/1250000000 : ℝ)] ![(677342354329/1562500000000 : ℝ), (50133151537403/100000000000000 : ℝ), (814617221039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194696693/10000000000 : ℝ)|^4731 ≤ (677342354329/1562500000000 : ℝ)^3707
        have hw : |(5194696693/10000000000 : ℝ)|=(5194696693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46571621/80000000 : ℝ)|^4731 ≤ (50133151537403/100000000000000 : ℝ)^3707
        have hw : |(46571621/80000000 : ℝ)|=(46571621/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147111831/1250000000 : ℝ)|^4731 ≤ (814617221039/12500000000000 : ℝ)^3707
        have hw : |(-147111831/1250000000 : ℝ)|=(147111831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s0_7 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1030067059/2500000000 : ℝ)*x 0 + (2674338451/5000000000 : ℝ)*x 1 + (1567306499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030067059/2500000000 : ℝ)^4731 ≤ (201574122107/625000000000 : ℝ)^3707 := by
    have hnat : (1030067059 : ℕ)^4731*625000000000^3707 ≤ 201574122107^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030067059 2500000000 201574122107 625000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2674338451/5000000000 : ℝ)^4731 ≤ (11249124875551/25000000000000 : ℝ)^3707 := by
    have hnat : (2674338451 : ℕ)^4731*25000000000000^3707 ≤ 11249124875551^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674338451 5000000000 11249124875551 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1567306499/5000000000 : ℝ)^4731 ≤ (5687910238753/25000000000000 : ℝ)^3707 := by
    have hnat : (1567306499 : ℕ)^4731*25000000000000^3707 ≤ 5687910238753^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567306499 5000000000 5687910238753 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030067059/2500000000 : ℝ), (2674338451/5000000000 : ℝ), (1567306499/5000000000 : ℝ)] ![(201574122107/625000000000 : ℝ), (11249124875551/25000000000000 : ℝ), (5687910238753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030067059/2500000000 : ℝ)|^4731 ≤ (201574122107/625000000000 : ℝ)^3707
        have hw : |(1030067059/2500000000 : ℝ)|=(1030067059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2674338451/5000000000 : ℝ)|^4731 ≤ (11249124875551/25000000000000 : ℝ)^3707
        have hw : |(2674338451/5000000000 : ℝ)|=(2674338451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1567306499/5000000000 : ℝ)|^4731 ≤ (5687910238753/25000000000000 : ℝ)^3707
        have hw : |(1567306499/5000000000 : ℝ)|=(1567306499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1603_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3869/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6101/25000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4727/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4727 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4727*1^1024 ≤ 0^1024*1^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4727/1024 : ℝ) ≤ (1455542797244697487/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4727 ≤ (1455542797244697487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4727*100000000000000000000^1024 ≤ 1455542797244697487^1024*5^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1455542797244697487 100000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1455542797244697487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4727 := by
      have hnat : (1 : ℕ)^1024*1^4727 ≤ 1^4727*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101455542797244697487/100000000000000000000 : ℝ) ≤ (1253919111418689/1250000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (101455542797244697487/100000000000000000000 : ℝ)^1024 ≤ (1253919111418689/1250000000000000 : ℝ)^4727 := by
      have hnat : (101455542797244697487 : ℕ)^1024*1250000000000000^4727 ≤ 1253919111418689^4727*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101455542797244697487 100000000000000000000 1253919111418689 1250000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253919111418689/1250000000000000 : ℝ)) (X := (101455542797244697487/100000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51455542797244697487/50000000000000000000 : ℝ) ≤ (628919111418689/625000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (51455542797244697487/50000000000000000000 : ℝ)^1024 ≤ (628919111418689/625000000000000 : ℝ)^4727 := by
      have hnat : (51455542797244697487 : ℕ)^1024*625000000000000^4727 ≤ 628919111418689^4727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51455542797244697487 50000000000000000000 628919111418689 625000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628919111418689/625000000000000 : ℝ)) (X := (51455542797244697487/50000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3919111418689/500000000000000 : ℝ)*(0 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3919111418689/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1455542797244697487/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3919111418689/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4727/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3919111418689/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1253919111418689/1250000000000000 : ℝ) by norm_num, show 1+(1455542797244697487/100000000000000000000 : ℝ)+(0 : ℝ)=(101455542797244697487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1455542797244697487/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3919111418689/500000000000000 : ℝ)*(2/5 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3919111418689/500000000000000 : ℝ)*(2/5 : ℝ)=(628919111418689/625000000000000 : ℝ) by norm_num, show 1+2*(1455542797244697487/100000000000000000000 : ℝ)=(51455542797244697487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3919111418689/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3919111418689/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3919111418689/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3919111418689/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3919111418689/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3919111418689/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-157883963/1000000000 : ℝ)*X 0 0+(5846673329/10000000000 : ℝ)*X 0 1+(977545051/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2728306123/5000000000 : ℝ)*X 1 0+(-2110622469/10000000000 : ℝ)*X 1 1+(4887725107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1364153029/2500000000 : ℝ)*X 2 0+(122193129/250000000 : ℝ)*X 2 1+(-2110622571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4113230943/10000000000 : ℝ)*X 0 0+(384151089/1250000000 : ℝ)*X 0 1+(5407966657/10000000000 : ℝ)*X 0 2+(4113230943/10000000000 : ℝ)*X 1 0+(384151089/1250000000 : ℝ)*X 1 1+(5407966657/10000000000 : ℝ)*X 1 2+(4113230943/10000000000 : ℝ)*X 2 0+(384151089/1250000000 : ℝ)*X 2 1+(5407966657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-790864761/5000000000 : ℝ)*X 0 0+(4912077357/10000000000 : ℝ)*X 0 1+(1455363151/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324668537/625000000 : ℝ)*X 1 0+(-1176894357/10000000000 : ℝ)*X 1 1+(582145291/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5194696693/10000000000 : ℝ)*X 2 0+(46571621/80000000 : ℝ)*X 2 1+(-147111831/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1030067059/2500000000 : ℝ)*X 0 0+(2674338451/5000000000 : ℝ)*X 0 1+(1567306499/5000000000 : ℝ)*X 0 2+(1030067059/2500000000 : ℝ)*X 1 0+(2674338451/5000000000 : ℝ)*X 1 1+(1567306499/5000000000 : ℝ)*X 1 2+(1030067059/2500000000 : ℝ)*X 2 0+(2674338451/5000000000 : ℝ)*X 2 1+(1567306499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28890838082305505057547/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5418723/100000000000000 : ℝ)*(base1) + (207139387/50000000000000 : ℝ)*(base19) + (194717253/50000000000000 : ℝ)*(base23) + (35236819/50000000000000 : ℝ)*(upper3) + (125193/390625000000 : ℝ)*(upper5) + (367780896878559/50000000000000 : ℝ)*(major0) + (367780896878559/50000000000000 : ℝ)*(major1) + (367780896878559/50000000000000 : ℝ)*(major2) + (65175681811047/6250000000000 : ℝ)*(sp0) + (208562361819237/20000000000000 : ℝ)*(sp1) + (1042811833940453/100000000000000 : ℝ)*(sp2) + (1673088030123/390625000000 : ℝ)*(sp3) + (1319816931/100000000000000 : ℝ)*(sp4) + (372983413/50000000000000 : ℝ)*(sp7) + (428311287097037/100000000000000 : ℝ)*(f.failure) + (1042812223374959/100000000000000 : ℝ)*(f.sum) + (4233068764151/12500000000000000000000000000 : ℝ)*base65 + (25316353914151/25000000000000000000000000000 : ℝ)*base67 + (19420015210849/25000000000000000000000000000 : ℝ)*base70 + (79609395239151/25000000000000000000000000000 : ℝ)*base71 + (23842710798349/12500000000000000000000000000 : ℝ)*base74 + (288807317014151/25000000000000000000000000000 : ℝ)*base75 + (114623219289151/25000000000000000000000000000 : ℝ)*base77 + (292313386289151/25000000000000000000000000000 : ℝ)*base79 + (54831955273349/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (531973/312500000000000000000 : ℝ)*base89 + (531973/312500000000000000000 : ℝ)*base91 + (531973/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153494226575777294067/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (55093099/100000000000000 : ℝ)*(base1) + (105504771/20000000000000 : ℝ)*(base19) + (550846519/100000000000000 : ℝ)*(base23) + (17260031/25000000000000 : ℝ)*(base32) + (48369517/50000000000000 : ℝ)*(upper3) + (7756567732291/1000000000000 : ℝ)*(major0) + (7756567732291/1000000000000 : ℝ)*(major1) + (7756567732291/1000000000000 : ℝ)*(major2) + (2620263/195312500000 : ℝ)*(sp1) + (1380096049/100000000000000 : ℝ)*(sp2) + (1099655271928047/100000000000000 : ℝ)*(sp4) + (1099653347736437/100000000000000 : ℝ)*(sp5) + (54982664294619/5000000000000 : ℝ)*(sp6) + (451658123626433/100000000000000 : ℝ)*(sp7) + (451658247759657/100000000000000 : ℝ)*(f.failure) + (274913804208737/25000000000000 : ℝ)*(f.sum) + (495521522999/250000000000000000000000000 : ℝ)*base65 + (4267725013999/500000000000000000000000000 : ℝ)*base67 + (3757085925499/500000000000000000000000000 : ℝ)*base69 + (1265145052499/500000000000000000000000000 : ℝ)*base71 + (1690411463249/250000000000000000000000000 : ℝ)*base73 + (1345093188499/500000000000000000000000000 : ℝ)*base75 + (3712110580499/500000000000000000000000000 : ℝ)*base77 + (1502495733499/500000000000000000000000000 : ℝ)*base79 + (1129348207749/250000000000000000000000000 : ℝ)*base81 + (1248047/312500000000000000000 : ℝ)*base90 + (1248047/312500000000000000000 : ℝ)*base92 + (1248047/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1603_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3869/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6101/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1603_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1603_s1_0 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1705520947/10000000000 : ℝ)*x 0 + (1107318263/2000000000 : ℝ)*x 1 + (2557971207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1705520947/10000000000 : ℝ)^4731 ≤ (10463325690589/100000000000000 : ℝ)^3707 := by
    have hnat : (1705520947 : ℕ)^4731*100000000000000^3707 ≤ 10463325690589^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705520947 10000000000 10463325690589 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107318263/2000000000 : ℝ)^4731 ≤ (23511875435493/50000000000000 : ℝ)^3707 := by
    have hnat : (1107318263 : ℕ)^4731*50000000000000^3707 ≤ 23511875435493^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107318263 2000000000 23511875435493 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2557971207/5000000000 : ℝ)^4731 ≤ (10628230855631/25000000000000 : ℝ)^3707 := by
    have hnat : (2557971207 : ℕ)^4731*25000000000000^3707 ≤ 10628230855631^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557971207 5000000000 10628230855631 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1705520947/10000000000 : ℝ), (1107318263/2000000000 : ℝ), (2557971207/5000000000 : ℝ)] ![(10463325690589/100000000000000 : ℝ), (23511875435493/50000000000000 : ℝ), (10628230855631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1705520947/10000000000 : ℝ)|^4731 ≤ (10463325690589/100000000000000 : ℝ)^3707
        have hw : |(-1705520947/10000000000 : ℝ)|=(1705520947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107318263/2000000000 : ℝ)|^4731 ≤ (23511875435493/50000000000000 : ℝ)^3707
        have hw : |(1107318263/2000000000 : ℝ)|=(1107318263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2557971207/5000000000 : ℝ)|^4731 ≤ (10628230855631/25000000000000 : ℝ)^3707
        have hw : |(2557971207/5000000000 : ℝ)|=(2557971207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_1 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374073327/10000000000 : ℝ)*x 0 + (-481444969/2500000000 : ℝ)*x 1 + (39968299/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374073327/10000000000 : ℝ)^4731 ≤ (45269346830933/100000000000000 : ℝ)^3707 := by
    have hnat : (5374073327 : ℕ)^4731*100000000000000^3707 ≤ 45269346830933^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374073327 10000000000 45269346830933 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481444969/2500000000 : ℝ)^4731 ≤ (12217731236769/100000000000000 : ℝ)^3707 := by
    have hnat : (481444969 : ℕ)^4731*100000000000000^3707 ≤ 12217731236769^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481444969 2500000000 12217731236769 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39968299/78125000 : ℝ)^4731 ≤ (21256460958281/50000000000000 : ℝ)^3707 := by
    have hnat : (39968299 : ℕ)^4731*50000000000000^3707 ≤ 21256460958281^3707*78125000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39968299 78125000 21256460958281 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374073327/10000000000 : ℝ), (-481444969/2500000000 : ℝ), (39968299/78125000 : ℝ)] ![(45269346830933/100000000000000 : ℝ), (12217731236769/100000000000000 : ℝ), (21256460958281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374073327/10000000000 : ℝ)|^4731 ≤ (45269346830933/100000000000000 : ℝ)^3707
        have hw : |(5374073327/10000000000 : ℝ)|=(5374073327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-481444969/2500000000 : ℝ)|^4731 ≤ (12217731236769/100000000000000 : ℝ)^3707
        have hw : |(-481444969/2500000000 : ℝ)|=(481444969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39968299/78125000 : ℝ)|^4731 ≤ (21256460958281/50000000000000 : ℝ)^3707
        have hw : |(39968299/78125000 : ℝ)|=(39968299/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_2 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343518237/2500000000 : ℝ)*x 0 + (5115942599/10000000000 : ℝ)*x 1 + (-38515599/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343518237/2500000000 : ℝ)^4731 ≤ (45269342756471/100000000000000 : ℝ)^3707 := by
    have hnat : (1343518237 : ℕ)^4731*100000000000000^3707 ≤ 45269342756471^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343518237 2500000000 45269342756471 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5115942599/10000000000 : ℝ)^4731 ≤ (42512925384517/100000000000000 : ℝ)^3707 := by
    have hnat : (5115942599 : ℕ)^4731*100000000000000^3707 ≤ 42512925384517^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115942599 10000000000 42512925384517 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38515599/200000000 : ℝ)^4731 ≤ (12217731835933/100000000000000 : ℝ)^3707 := by
    have hnat : (38515599 : ℕ)^4731*100000000000000^3707 ≤ 12217731835933^3707*200000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38515599 200000000 12217731835933 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343518237/2500000000 : ℝ), (5115942599/10000000000 : ℝ), (-38515599/200000000 : ℝ)] ![(45269342756471/100000000000000 : ℝ), (42512925384517/100000000000000 : ℝ), (12217731835933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343518237/2500000000 : ℝ)|^4731 ≤ (45269342756471/100000000000000 : ℝ)^3707
        have hw : |(1343518237/2500000000 : ℝ)|=(1343518237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5115942599/10000000000 : ℝ)|^4731 ≤ (42512925384517/100000000000000 : ℝ)^3707
        have hw : |(5115942599/10000000000 : ℝ)|=(5115942599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38515599/200000000 : ℝ)|^4731 ≤ (12217731835933/100000000000000 : ℝ)^3707
        have hw : |(-38515599/200000000 : ℝ)|=(38515599/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_3 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420628983/1000000000 : ℝ)*x 0 + (3718399779/10000000000 : ℝ)*x 1 + (4742556493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420628983/1000000000 : ℝ)^4731 ≤ (33113669274723/100000000000000 : ℝ)^3707 := by
    have hnat : (420628983 : ℕ)^4731*100000000000000^3707 ≤ 33113669274723^3707*1000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420628983 1000000000 33113669274723 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3718399779/10000000000 : ℝ)^4731 ≤ (28292658462899/100000000000000 : ℝ)^3707 := by
    have hnat : (3718399779 : ℕ)^4731*100000000000000^3707 ≤ 28292658462899^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718399779 10000000000 28292658462899 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4742556493/10000000000 : ℝ)^4731 ≤ (154374688959/400000000000 : ℝ)^3707 := by
    have hnat : (4742556493 : ℕ)^4731*400000000000^3707 ≤ 154374688959^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742556493 10000000000 154374688959 400000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420628983/1000000000 : ℝ), (3718399779/10000000000 : ℝ), (4742556493/10000000000 : ℝ)] ![(33113669274723/100000000000000 : ℝ), (28292658462899/100000000000000 : ℝ), (154374688959/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420628983/1000000000 : ℝ)|^4731 ≤ (33113669274723/100000000000000 : ℝ)^3707
        have hw : |(420628983/1000000000 : ℝ)|=(420628983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3718399779/10000000000 : ℝ)|^4731 ≤ (28292658462899/100000000000000 : ℝ)^3707
        have hw : |(3718399779/10000000000 : ℝ)|=(3718399779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4742556493/10000000000 : ℝ)|^4731 ≤ (154374688959/400000000000 : ℝ)^3707
        have hw : |(4742556493/10000000000 : ℝ)|=(4742556493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_4 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1705759021/10000000000 : ℝ)*x 0 + (2560291061/5000000000 : ℝ)*x 1 + (172871209/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1705759021/10000000000 : ℝ)^4731 ≤ (5232594882811/50000000000000 : ℝ)^3707 := by
    have hnat : (1705759021 : ℕ)^4731*50000000000000^3707 ≤ 5232594882811^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705759021 10000000000 5232594882811 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560291061/5000000000 : ℝ)^4731 ≤ (10640533847227/25000000000000 : ℝ)^3707 := by
    have hnat : (2560291061 : ℕ)^4731*25000000000000^3707 ≤ 10640533847227^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560291061 5000000000 10640533847227 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172871209/312500000 : ℝ)^4731 ≤ (23486337418943/50000000000000 : ℝ)^3707 := by
    have hnat : (172871209 : ℕ)^4731*50000000000000^3707 ≤ 23486337418943^3707*312500000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172871209 312500000 23486337418943 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1705759021/10000000000 : ℝ), (2560291061/5000000000 : ℝ), (172871209/312500000 : ℝ)] ![(5232594882811/50000000000000 : ℝ), (10640533847227/25000000000000 : ℝ), (23486337418943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1705759021/10000000000 : ℝ)|^4731 ≤ (5232594882811/50000000000000 : ℝ)^3707
        have hw : |(-1705759021/10000000000 : ℝ)|=(1705759021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2560291061/5000000000 : ℝ)|^4731 ≤ (10640533847227/25000000000000 : ℝ)^3707
        have hw : |(2560291061/5000000000 : ℝ)|=(2560291061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172871209/312500000 : ℝ)|^4731 ≤ (23486337418943/50000000000000 : ℝ)^3707
        have hw : |(172871209/312500000 : ℝ)|=(172871209/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_5 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262291553/10000000000 : ℝ)*x 0 + (-1509843333/10000000000 : ℝ)*x 1 + (553187899/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262291553/10000000000 : ℝ)^4731 ≤ (22035550122449/50000000000000 : ℝ)^3707 := by
    have hnat : (5262291553 : ℕ)^4731*50000000000000^3707 ≤ 22035550122449^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262291553 10000000000 22035550122449 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1509843333/10000000000 : ℝ)^4731 ≤ (8956221620941/100000000000000 : ℝ)^3707 := by
    have hnat : (1509843333 : ℕ)^4731*100000000000000^3707 ≤ 8956221620941^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509843333 10000000000 8956221620941 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553187899/1000000000 : ℝ)^4731 ≤ (9394535622123/20000000000000 : ℝ)^3707 := by
    have hnat : (553187899 : ℕ)^4731*20000000000000^3707 ≤ 9394535622123^3707*1000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553187899 1000000000 9394535622123 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262291553/10000000000 : ℝ), (-1509843333/10000000000 : ℝ), (553187899/1000000000 : ℝ)] ![(22035550122449/50000000000000 : ℝ), (8956221620941/100000000000000 : ℝ), (9394535622123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262291553/10000000000 : ℝ)|^4731 ≤ (22035550122449/50000000000000 : ℝ)^3707
        have hw : |(5262291553/10000000000 : ℝ)|=(5262291553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1509843333/10000000000 : ℝ)|^4731 ≤ (8956221620941/100000000000000 : ℝ)^3707
        have hw : |(-1509843333/10000000000 : ℝ)|=(1509843333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553187899/1000000000 : ℝ)|^4731 ≤ (9394535622123/20000000000000 : ℝ)^3707
        have hw : |(553187899/1000000000 : ℝ)|=(553187899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_6 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631145483/5000000000 : ℝ)*x 0 + (5531879209/10000000000 : ℝ)*x 1 + (-1509843849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631145483/5000000000 : ℝ)^4731 ≤ (5508886746357/12500000000000 : ℝ)^3707 := by
    have hnat : (2631145483 : ℕ)^4731*12500000000000^3707 ≤ 5508886746357^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631145483 5000000000 5508886746357 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5531879209/10000000000 : ℝ)^4731 ≤ (11743170120971/25000000000000 : ℝ)^3707 := by
    have hnat : (5531879209 : ℕ)^4731*25000000000000^3707 ≤ 11743170120971^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531879209 10000000000 11743170120971 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1509843849/10000000000 : ℝ)^4731 ≤ (2239056381827/25000000000000 : ℝ)^3707 := by
    have hnat : (1509843849 : ℕ)^4731*25000000000000^3707 ≤ 2239056381827^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509843849 10000000000 2239056381827 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631145483/5000000000 : ℝ), (5531879209/10000000000 : ℝ), (-1509843849/10000000000 : ℝ)] ![(5508886746357/12500000000000 : ℝ), (11743170120971/25000000000000 : ℝ), (2239056381827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631145483/5000000000 : ℝ)|^4731 ≤ (5508886746357/12500000000000 : ℝ)^3707
        have hw : |(2631145483/5000000000 : ℝ)|=(2631145483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5531879209/10000000000 : ℝ)|^4731 ≤ (11743170120971/25000000000000 : ℝ)^3707
        have hw : |(5531879209/10000000000 : ℝ)|=(5531879209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1509843849/10000000000 : ℝ)|^4731 ≤ (2239056381827/25000000000000 : ℝ)^3707
        have hw : |(-1509843849/10000000000 : ℝ)|=(1509843849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s1_7 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206868561/10000000000 : ℝ)*x 0 + (2365630583/5000000000 : ℝ)*x 1 + (3729872623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206868561/10000000000 : ℝ)^4731 ≤ (33119483923321/100000000000000 : ℝ)^3707 := by
    have hnat : (4206868561 : ℕ)^4731*100000000000000^3707 ≤ 33119483923321^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206868561 10000000000 33119483923321 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2365630583/5000000000 : ℝ)^4731 ≤ (9619100366303/25000000000000 : ℝ)^3707 := by
    have hnat : (2365630583 : ℕ)^4731*25000000000000^3707 ≤ 9619100366303^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365630583 5000000000 9619100366303 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3729872623/10000000000 : ℝ)^4731 ≤ (7101028652401/25000000000000 : ℝ)^3707 := by
    have hnat : (3729872623 : ℕ)^4731*25000000000000^3707 ≤ 7101028652401^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729872623 10000000000 7101028652401 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206868561/10000000000 : ℝ), (2365630583/5000000000 : ℝ), (3729872623/10000000000 : ℝ)] ![(33119483923321/100000000000000 : ℝ), (9619100366303/25000000000000 : ℝ), (7101028652401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206868561/10000000000 : ℝ)|^4731 ≤ (33119483923321/100000000000000 : ℝ)^3707
        have hw : |(4206868561/10000000000 : ℝ)|=(4206868561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2365630583/5000000000 : ℝ)|^4731 ≤ (9619100366303/25000000000000 : ℝ)^3707
        have hw : |(2365630583/5000000000 : ℝ)|=(2365630583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3729872623/10000000000 : ℝ)|^4731 ≤ (7101028652401/25000000000000 : ℝ)^3707
        have hw : |(3729872623/10000000000 : ℝ)|=(3729872623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1603_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6101/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17913/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6101/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3869/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6101/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3869/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6101/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3869/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6101/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3869/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6101/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3869/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6101/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3869/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3869/100000 : ℝ) ^ (4727/1024 : ℝ) ≤ (30203537264063/100000000000000000000 : ℝ) := by
    have hpowers : (3869/100000 : ℝ)^4727 ≤ (30203537264063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4727*100000000000000000000^1024 ≤ 30203537264063^1024*100000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 100000 30203537264063 100000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/100000 : ℝ)) (X := (30203537264063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6101/25000 : ℝ) ^ (4727/1024 : ℝ) ≤ (37181837848779669/25000000000000000000 : ℝ) := by
    have hpowers : (6101/25000 : ℝ)^4727 ≤ (37181837848779669/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6101 : ℕ)^4727*25000000000000000000^1024 ≤ 37181837848779669^1024*25000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6101 25000 37181837848779669 25000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6101/25000 : ℝ)) (X := (37181837848779669/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000030203537264063/50000000000000000000 : ℝ) ≤ (5000000654292677/5000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (50000030203537264063/50000000000000000000 : ℝ)^1024 ≤ (5000000654292677/5000000000000000 : ℝ)^4727 := by
      have hnat : (50000030203537264063 : ℕ)^1024*5000000000000000^4727 ≤ 5000000654292677^4727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000030203537264063 50000000000000000000 5000000654292677 5000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000654292677/5000000000000000 : ℝ)) (X := (50000030203537264063/50000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100148757554932382739/100000000000000000000 : ℝ) ≤ (2500805156859429/2500000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (100148757554932382739/100000000000000000000 : ℝ)^1024 ≤ (2500805156859429/2500000000000000 : ℝ)^4727 := by
      have hnat : (100148757554932382739 : ℕ)^1024*2500000000000000^4727 ≤ 2500805156859429^4727*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100148757554932382739 100000000000000000000 2500805156859429 2500000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500805156859429/2500000000000000 : ℝ)) (X := (100148757554932382739/100000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12537181837848779669/12500000000000000000 : ℝ) ≤ (5003219973145039/5000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (12537181837848779669/12500000000000000000 : ℝ)^1024 ≤ (5003219973145039/5000000000000000 : ℝ)^4727 := by
      have hnat : (12537181837848779669 : ℕ)^1024*5000000000000000^4727 ≤ 5003219973145039^4727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12537181837848779669 12500000000000000000 5003219973145039 5000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003219973145039/5000000000000000 : ℝ)) (X := (12537181837848779669/12500000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30203537264063/100000000000000000000 : ℝ) ≤ ((102662557891260333617/102675000000000000000 : ℝ)+2*(1609659426181/1026750000000000 : ℝ)*(3869/100000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (102662557891260333617/102675000000000000000 : ℝ)+2*(1609659426181/1026750000000000 : ℝ)*(3869/100000 : ℝ)=(5000000654292677/5000000000000000 : ℝ) by norm_num, show 1+2*(30203537264063/100000000000000000000 : ℝ)=(50000030203537264063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37181837848779669/25000000000000000000 : ℝ)+(30203537264063/100000000000000000000 : ℝ) ≤ ((102662557891260333617/102675000000000000000 : ℝ)+(1609659426181/1026750000000000 : ℝ)*((6101/25000 : ℝ)+(3869/100000 : ℝ)))^(4727/1024 : ℝ) := by
    rw [show (102662557891260333617/102675000000000000000 : ℝ)+(1609659426181/1026750000000000 : ℝ)*((6101/25000 : ℝ)+(3869/100000 : ℝ))=(2500805156859429/2500000000000000 : ℝ) by norm_num, show 1+(37181837848779669/25000000000000000000 : ℝ)+(30203537264063/100000000000000000000 : ℝ)=(100148757554932382739/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37181837848779669/25000000000000000000 : ℝ) ≤ ((102662557891260333617/102675000000000000000 : ℝ)+2*(1609659426181/1026750000000000 : ℝ)*(6101/25000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (102662557891260333617/102675000000000000000 : ℝ)+2*(1609659426181/1026750000000000 : ℝ)*(6101/25000 : ℝ)=(5003219973145039/5000000000000000 : ℝ) by norm_num, show 1+2*(37181837848779669/25000000000000000000 : ℝ)=(12537181837848779669/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (102662557891260333617/102675000000000000000 : ℝ)*(X 1 0+X 2 0)+(1609659426181/1026750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (3869/100000 : ℝ)) (hi := (6101/25000 : ℝ)) (c := (102662557891260333617/102675000000000000000 : ℝ)) (alpha := (1609659426181/1026750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (102662557891260333617/102675000000000000000 : ℝ)*(X 0 1+X 2 1)+(1609659426181/1026750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (3869/100000 : ℝ)) (hi := (6101/25000 : ℝ)) (c := (102662557891260333617/102675000000000000000 : ℝ)) (alpha := (1609659426181/1026750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (102662557891260333617/102675000000000000000 : ℝ)*(X 0 2+X 1 2)+(1609659426181/1026750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (3869/100000 : ℝ)) (hi := (6101/25000 : ℝ)) (c := (102662557891260333617/102675000000000000000 : ℝ)) (alpha := (1609659426181/1026750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1705520947/10000000000 : ℝ)*X 0 0+(1107318263/2000000000 : ℝ)*X 0 1+(2557971207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374073327/10000000000 : ℝ)*X 1 0+(-481444969/2500000000 : ℝ)*X 1 1+(39968299/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343518237/2500000000 : ℝ)*X 2 0+(5115942599/10000000000 : ℝ)*X 2 1+(-38515599/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((420628983/1000000000 : ℝ)*X 0 0+(3718399779/10000000000 : ℝ)*X 0 1+(4742556493/10000000000 : ℝ)*X 0 2+(420628983/1000000000 : ℝ)*X 1 0+(3718399779/10000000000 : ℝ)*X 1 1+(4742556493/10000000000 : ℝ)*X 1 2+(420628983/1000000000 : ℝ)*X 2 0+(3718399779/10000000000 : ℝ)*X 2 1+(4742556493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1705759021/10000000000 : ℝ)*X 0 0+(2560291061/5000000000 : ℝ)*X 0 1+(172871209/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5262291553/10000000000 : ℝ)*X 1 0+(-1509843333/10000000000 : ℝ)*X 1 1+(553187899/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631145483/5000000000 : ℝ)*X 2 0+(5531879209/10000000000 : ℝ)*X 2 1+(-1509843849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206868561/10000000000 : ℝ)*X 0 0+(2365630583/5000000000 : ℝ)*X 0 1+(3729872623/10000000000 : ℝ)*X 0 2+(4206868561/10000000000 : ℝ)*X 1 0+(2365630583/5000000000 : ℝ)*X 1 1+(3729872623/10000000000 : ℝ)*X 1 2+(4206868561/10000000000 : ℝ)*X 2 0+(2365630583/5000000000 : ℝ)*X 2 1+(3729872623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319663985219010342095948403/34225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27126927/25000000000000 : ℝ)*(base1) + (196585829/10000000000000 : ℝ)*(base19) + (224775183/12500000000000 : ℝ)*(base23) + (122752111/50000000000000 : ℝ)*(upper3) + (174037927/100000000000000 : ℝ)*(upper5) + (33537371120059/2000000000000 : ℝ)*(major0) + (33537371120059/2000000000000 : ℝ)*(major1) + (33537371120059/2000000000000 : ℝ)*(major2) + (1188647889828807/50000000000000 : ℝ)*(sp0) + (594327185087311/25000000000000 : ℝ)*(sp1) + (237730890800607/10000000000000 : ℝ)*(sp2) + (976419348180857/100000000000000 : ℝ)*(sp3) + (15035057629/100000000000000 : ℝ)*(sp4) + (6637774043/100000000000000 : ℝ)*(sp7) + (61026630903913/6250000000000 : ℝ)*(f.failure) + (1188655353103767/50000000000000 : ℝ)*(f.sum) + (680866937623/2053500000000000000000000000 : ℝ)*base66 + (32391367345842199/68450000000000000000000000000000 : ℝ)*base68 + (439823177534892199/68450000000000000000000000000000 : ℝ)*base70 + (21404138321242199/68450000000000000000000000000000 : ℝ)*base72 + (11673779345963/4107000000000000000000000000 : ℝ)*base74 + (49916624766107801/68450000000000000000000000000000 : ℝ)*base75 + (59857950024642199/68450000000000000000000000000000 : ℝ)*base78 + (103109187326257801/68450000000000000000000000000000 : ℝ)*base79 + (5677849779907/2053500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (30649/9765625000000000000 : ℝ)*base90 + (30649/9765625000000000000 : ℝ)*base92 + (30649/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21468481081750966958572739/2890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186264529/12500000000000 : ℝ)*(base19) + (1267726713/100000000000000 : ℝ)*(base23) + (1165793/3125000000000 : ℝ)*(upper2) + (272557299/100000000000000 : ℝ)*(upper3) + (6466783/6250000000000 : ℝ)*(upper5) + (107185805079793/6250000000000 : ℝ)*(major0) + (107185805079793/6250000000000 : ℝ)*(major1) + (107185805079793/6250000000000 : ℝ)*(major2) + (2804939181/25000000000000 : ℝ)*(sp1) + (2545184261/25000000000000 : ℝ)*(sp2) + (1215665800315353/50000000000000 : ℝ)*(sp4) + (9725275563031/400000000000 : ℝ)*(sp5) + (48626403043339/2000000000000 : ℝ)*(sp6) + (998613914358197/100000000000000 : ℝ)*(sp7) + (998613914358197/100000000000000 : ℝ)*(f.failure) + (1215665800315353/50000000000000 : ℝ)*(f.sum) + (69252363013631/102675000000000000000000000000 : ℝ)*base65 + (1146770529770362073/213906250000000000000000000000000 : ℝ)*base68 + (607046263774268323/213906250000000000000000000000000 : ℝ)*base70 + (429289433331143323/213906250000000000000000000000000 : ℝ)*base72 + (4518775270043/12834375000000000000000000000 : ℝ)*base74 + (2402300606477393323/213906250000000000000000000000000 : ℝ)*base76 + (792731748841455823/213906250000000000000000000000000 : ℝ)*base78 + (3831516809240049573/213906250000000000000000000000000 : ℝ)*base80 + (360126870867881/102675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2227613/312500000000000000000 : ℝ)*base89 + (2227613/312500000000000000000 : ℝ)*base91 + (2227613/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1603_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6101/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17913/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1603_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1603_s2_0 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1720418241/10000000000 : ℝ)*x 0 + (34186307/62500000 : ℝ)*x 1 + (5172985133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1720418241/10000000000 : ℝ)^4731 ≤ (5290053449233/50000000000000 : ℝ)^3707 := by
    have hnat : (1720418241 : ℕ)^4731*50000000000000^3707 ≤ 5290053449233^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720418241 10000000000 5290053449233 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34186307/62500000 : ℝ)^4731 ≤ (9260216312817/20000000000000 : ℝ)^3707 := by
    have hnat : (34186307 : ℕ)^4731*20000000000000^3707 ≤ 9260216312817^3707*62500000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34186307 62500000 9260216312817 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172985133/10000000000 : ℝ)^4731 ≤ (10779702878527/25000000000000 : ℝ)^3707 := by
    have hnat : (5172985133 : ℕ)^4731*25000000000000^3707 ≤ 10779702878527^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172985133 10000000000 10779702878527 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1720418241/10000000000 : ℝ), (34186307/62500000 : ℝ), (5172985133/10000000000 : ℝ)] ![(5290053449233/50000000000000 : ℝ), (9260216312817/20000000000000 : ℝ), (10779702878527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1720418241/10000000000 : ℝ)|^4731 ≤ (5290053449233/50000000000000 : ℝ)^3707
        have hw : |(-1720418241/10000000000 : ℝ)|=(1720418241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34186307/62500000 : ℝ)|^4731 ≤ (9260216312817/20000000000000 : ℝ)^3707
        have hw : |(34186307/62500000 : ℝ)|=(34186307/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172985133/10000000000 : ℝ)|^4731 ≤ (10779702878527/25000000000000 : ℝ)^3707
        have hw : |(5172985133/10000000000 : ℝ)|=(5172985133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_1 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356725059/10000000000 : ℝ)*x 0 + (-936888963/5000000000 : ℝ)*x 1 + (129324629/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356725059/10000000000 : ℝ)^4731 ≤ (45082926490977/100000000000000 : ℝ)^3707 := by
    have hnat : (5356725059 : ℕ)^4731*100000000000000^3707 ≤ 45082926490977^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356725059 10000000000 45082926490977 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936888963/5000000000 : ℝ)^4731 ≤ (92173919487/781250000000 : ℝ)^3707 := by
    have hnat : (936888963 : ℕ)^4731*781250000000^3707 ≤ 92173919487^3707*5000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936888963 5000000000 92173919487 781250000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129324629/250000000 : ℝ)^4731 ≤ (10779702950333/25000000000000 : ℝ)^3707 := by
    have hnat : (129324629 : ℕ)^4731*25000000000000^3707 ≤ 10779702950333^3707*250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129324629 250000000 10779702950333 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356725059/10000000000 : ℝ), (-936888963/5000000000 : ℝ), (129324629/250000000 : ℝ)] ![(45082926490977/100000000000000 : ℝ), (92173919487/781250000000 : ℝ), (10779702950333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356725059/10000000000 : ℝ)|^4731 ≤ (45082926490977/100000000000000 : ℝ)^3707
        have hw : |(5356725059/10000000000 : ℝ)|=(5356725059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-936888963/5000000000 : ℝ)|^4731 ≤ (92173919487/781250000000 : ℝ)^3707
        have hw : |(-936888963/5000000000 : ℝ)|=(936888963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129324629/250000000 : ℝ)|^4731 ≤ (10779702950333/25000000000000 : ℝ)^3707
        have hw : |(129324629/250000000 : ℝ)|=(129324629/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_2 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356725087/10000000000 : ℝ)*x 0 + (5172985121/10000000000 : ℝ)*x 1 + (-93688897/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356725087/10000000000 : ℝ)^4731 ≤ (45082926791723/100000000000000 : ℝ)^3707 := by
    have hnat : (5356725087 : ℕ)^4731*100000000000000^3707 ≤ 45082926791723^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356725087 10000000000 45082926791723 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172985121/10000000000 : ℝ)^4731 ≤ (21559405693227/50000000000000 : ℝ)^3707 := by
    have hnat : (5172985121 : ℕ)^4731*50000000000000^3707 ≤ 21559405693227^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172985121 10000000000 21559405693227 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93688897/500000000 : ℝ)^4731 ≤ (11798261806837/100000000000000 : ℝ)^3707 := by
    have hnat : (93688897 : ℕ)^4731*100000000000000^3707 ≤ 11798261806837^3707*500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93688897 500000000 11798261806837 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356725087/10000000000 : ℝ), (5172985121/10000000000 : ℝ), (-93688897/500000000 : ℝ)] ![(45082926791723/100000000000000 : ℝ), (21559405693227/50000000000000 : ℝ), (11798261806837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356725087/10000000000 : ℝ)|^4731 ≤ (45082926791723/100000000000000 : ℝ)^3707
        have hw : |(5356725087/10000000000 : ℝ)|=(5356725087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172985121/10000000000 : ℝ)|^4731 ≤ (21559405693227/50000000000000 : ℝ)^3707
        have hw : |(5172985121/10000000000 : ℝ)|=(5172985121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93688897/500000000 : ℝ)|^4731 ≤ (11798261806837/100000000000000 : ℝ)^3707
        have hw : |(-93688897/500000000 : ℝ)|=(93688897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_3 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4217260579/10000000000 : ℝ)*x 0 + (3867967147/10000000000 : ℝ)*x 1 + (1147661621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217260579/10000000000 : ℝ)^4731 ≤ (33223932597297/100000000000000 : ℝ)^3707 := by
    have hnat : (4217260579 : ℕ)^4731*100000000000000^3707 ≤ 33223932597297^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217260579 10000000000 33223932597297 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3867967147/10000000000 : ℝ)^4731 ≤ (29753045848879/100000000000000 : ℝ)^3707 := by
    have hnat : (3867967147 : ℕ)^4731*100000000000000^3707 ≤ 29753045848879^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867967147 10000000000 29753045848879 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147661621/2500000000 : ℝ)^4731 ≤ (7404604308887/20000000000000 : ℝ)^3707 := by
    have hnat : (1147661621 : ℕ)^4731*20000000000000^3707 ≤ 7404604308887^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147661621 2500000000 7404604308887 20000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217260579/10000000000 : ℝ), (3867967147/10000000000 : ℝ), (1147661621/2500000000 : ℝ)] ![(33223932597297/100000000000000 : ℝ), (29753045848879/100000000000000 : ℝ), (7404604308887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217260579/10000000000 : ℝ)|^4731 ≤ (33223932597297/100000000000000 : ℝ)^3707
        have hw : |(4217260579/10000000000 : ℝ)|=(4217260579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3867967147/10000000000 : ℝ)|^4731 ≤ (29753045848879/100000000000000 : ℝ)^3707
        have hw : |(3867967147/10000000000 : ℝ)|=(3867967147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147661621/2500000000 : ℝ)|^4731 ≤ (7404604308887/20000000000000 : ℝ)^3707
        have hw : |(1147661621/2500000000 : ℝ)|=(1147661621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_4 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1720501741/10000000000 : ℝ)*x 0 + (1293825707/2500000000 : ℝ)*x 1 + (5467465929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1720501741/10000000000 : ℝ)^4731 ≤ (10580762252181/100000000000000 : ℝ)^3707 := by
    have hnat : (1720501741 : ℕ)^4731*100000000000000^3707 ≤ 10580762252181^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720501741 10000000000 10580762252181 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293825707/2500000000 : ℝ)^4731 ≤ (43143468447879/100000000000000 : ℝ)^3707 := by
    have hnat : (1293825707 : ℕ)^4731*100000000000000^3707 ≤ 43143468447879^3707*2500000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293825707 2500000000 43143468447879 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467465929/10000000000 : ℝ)^4731 ≤ (5784471160131/12500000000000 : ℝ)^3707 := by
    have hnat : (5467465929 : ℕ)^4731*12500000000000^3707 ≤ 5784471160131^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467465929 10000000000 5784471160131 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1720501741/10000000000 : ℝ), (1293825707/2500000000 : ℝ), (5467465929/10000000000 : ℝ)] ![(10580762252181/100000000000000 : ℝ), (43143468447879/100000000000000 : ℝ), (5784471160131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1720501741/10000000000 : ℝ)|^4731 ≤ (10580762252181/100000000000000 : ℝ)^3707
        have hw : |(-1720501741/10000000000 : ℝ)|=(1720501741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293825707/2500000000 : ℝ)|^4731 ≤ (43143468447879/100000000000000 : ℝ)^3707
        have hw : |(1293825707/2500000000 : ℝ)|=(1293825707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467465929/10000000000 : ℝ)|^4731 ≤ (5784471160131/12500000000000 : ℝ)^3707
        have hw : |(5467465929/10000000000 : ℝ)|=(5467465929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_5 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055596979/2000000000 : ℝ)*x 0 + (-98706071/625000000 : ℝ)*x 1 + (218698643/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055596979/2000000000 : ℝ)^4731 ≤ (11059726176947/25000000000000 : ℝ)^3707 := by
    have hnat : (1055596979 : ℕ)^4731*25000000000000^3707 ≤ 11059726176947^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055596979 2000000000 11059726176947 25000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98706071/625000000 : ℝ)^4731 ≤ (4742662204067/50000000000000 : ℝ)^3707 := by
    have hnat : (98706071 : ℕ)^4731*50000000000000^3707 ≤ 4742662204067^3707*625000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98706071 625000000 4742662204067 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218698643/400000000 : ℝ)^4731 ≤ (46275770858117/100000000000000 : ℝ)^3707 := by
    have hnat : (218698643 : ℕ)^4731*100000000000000^3707 ≤ 46275770858117^3707*400000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218698643 400000000 46275770858117 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055596979/2000000000 : ℝ), (-98706071/625000000 : ℝ), (218698643/400000000 : ℝ)] ![(11059726176947/25000000000000 : ℝ), (4742662204067/50000000000000 : ℝ), (46275770858117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055596979/2000000000 : ℝ)|^4731 ≤ (11059726176947/25000000000000 : ℝ)^3707
        have hw : |(1055596979/2000000000 : ℝ)|=(1055596979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98706071/625000000 : ℝ)|^4731 ≤ (4742662204067/50000000000000 : ℝ)^3707
        have hw : |(-98706071/625000000 : ℝ)|=(98706071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218698643/400000000 : ℝ)|^4731 ≤ (46275770858117/100000000000000 : ℝ)^3707
        have hw : |(218698643/400000000 : ℝ)|=(218698643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_6 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055597063/2000000000 : ℝ)*x 0 + (42714573/78125000 : ℝ)*x 1 + (-1579297583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055597063/2000000000 : ℝ)^4731 ≤ (691232956259/1562500000000 : ℝ)^3707 := by
    have hnat : (1055597063 : ℕ)^4731*1562500000000^3707 ≤ 691232956259^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055597063 2000000000 691232956259 1562500000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42714573/78125000 : ℝ)^4731 ≤ (46275762961969/100000000000000 : ℝ)^3707 := by
    have hnat : (42714573 : ℕ)^4731*100000000000000^3707 ≤ 46275762961969^3707*78125000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42714573 78125000 46275762961969 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1579297583/10000000000 : ℝ)^4731 ≤ (9485327834441/100000000000000 : ℝ)^3707 := by
    have hnat : (1579297583 : ℕ)^4731*100000000000000^3707 ≤ 9485327834441^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579297583 10000000000 9485327834441 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055597063/2000000000 : ℝ), (42714573/78125000 : ℝ), (-1579297583/10000000000 : ℝ)] ![(691232956259/1562500000000 : ℝ), (46275762961969/100000000000000 : ℝ), (9485327834441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055597063/2000000000 : ℝ)|^4731 ≤ (691232956259/1562500000000 : ℝ)^3707
        have hw : |(1055597063/2000000000 : ℝ)|=(1055597063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42714573/78125000 : ℝ)|^4731 ≤ (46275762961969/100000000000000 : ℝ)^3707
        have hw : |(42714573/78125000 : ℝ)|=(42714573/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1579297583/10000000000 : ℝ)|^4731 ≤ (9485327834441/100000000000000 : ℝ)^3707
        have hw : |(-1579297583/10000000000 : ℝ)|=(1579297583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1603_s2_7 (p : ℝ) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527183043/1250000000 : ℝ)*x 0 + (917000711/2000000000 : ℝ)*x 1 + (3873672639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527183043/1250000000 : ℝ)^4731 ≤ (4153247665159/12500000000000 : ℝ)^3707 := by
    have hnat : (527183043 : ℕ)^4731*12500000000000^3707 ≤ 4153247665159^3707*1250000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527183043 1250000000 4153247665159 12500000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917000711/2000000000 : ℝ)^4731 ≤ (18482475279453/50000000000000 : ℝ)^3707 := by
    have hnat : (917000711 : ℕ)^4731*50000000000000^3707 ≤ 18482475279453^3707*2000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917000711 2000000000 18482475279453 50000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3873672639/10000000000 : ℝ)^4731 ≤ (29809068100069/100000000000000 : ℝ)^3707 := by
    have hnat : (3873672639 : ℕ)^4731*100000000000000^3707 ≤ 29809068100069^3707*10000000000^4731 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3873672639 10000000000 29809068100069 100000000000000 4731 3707 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4731/1024 : ℝ)) 4731 3707 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527183043/1250000000 : ℝ), (917000711/2000000000 : ℝ), (3873672639/10000000000 : ℝ)] ![(4153247665159/12500000000000 : ℝ), (18482475279453/50000000000000 : ℝ), (29809068100069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527183043/1250000000 : ℝ)|^4731 ≤ (4153247665159/12500000000000 : ℝ)^3707
        have hw : |(527183043/1250000000 : ℝ)|=(527183043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917000711/2000000000 : ℝ)|^4731 ≤ (18482475279453/50000000000000 : ℝ)^3707
        have hw : |(917000711/2000000000 : ℝ)|=(917000711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3873672639/10000000000 : ℝ)|^4731 ≤ (29809068100069/100000000000000 : ℝ)^3707
        have hw : |(3873672639/10000000000 : ℝ)|=(3873672639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1603_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5117/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4131/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4501/50000 : ℝ) ^ (4727/1024 : ℝ) ≤ (372347380825251/25000000000000000000 : ℝ) := by
    have hpowers : (4501/50000 : ℝ)^4727 ≤ (372347380825251/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4501 : ℕ)^4727*25000000000000000000^1024 ≤ 372347380825251^1024*50000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4501 50000 372347380825251 25000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4501/50000 : ℝ)) (X := (372347380825251/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17913/100000 : ℝ) ^ (4727/1024 : ℝ) ≤ (17841750500510353/50000000000000000000 : ℝ) := by
    have hpowers : (17913/100000 : ℝ)^4727 ≤ (17841750500510353/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17913 : ℕ)^4727*50000000000000000000^1024 ≤ 17841750500510353^1024*100000^4727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17913 100000 17841750500510353 50000000000000000000 4727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17913/100000 : ℝ)) (X := (17841750500510353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500372347380825251/12500000000000000000 : ℝ) ≤ (5000032263953411/5000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (12500372347380825251/12500000000000000000 : ℝ)^1024 ≤ (5000032263953411/5000000000000000 : ℝ)^4727 := by
      have hnat : (12500372347380825251 : ℕ)^1024*5000000000000000^4727 ≤ 5000032263953411^4727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500372347380825251 12500000000000000000 5000032263953411 5000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032263953411/5000000000000000 : ℝ)) (X := (12500372347380825251/12500000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003717289052432171/10000000000000000000 : ℝ) ≤ (10000805151233601/10000000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (10003717289052432171/10000000000000000000 : ℝ)^1024 ≤ (10000805151233601/10000000000000000 : ℝ)^4727 := by
      have hnat : (10003717289052432171 : ℕ)^1024*10000000000000000^4727 ≤ 10000805151233601^4727*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003717289052432171 10000000000000000000 10000805151233601 10000000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000805151233601/10000000000000000 : ℝ)) (X := (10003717289052432171/10000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017841750500510353/25000000000000000000 : ℝ) ≤ (500077288728019/500000000000000 : ℝ) ^ (4727/1024 : ℝ) := by
    have hpowers : (25017841750500510353/25000000000000000000 : ℝ)^1024 ≤ (500077288728019/500000000000000 : ℝ)^4727 := by
      have hnat : (25017841750500510353 : ℕ)^1024*500000000000000^4727 ≤ 500077288728019^4727*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017841750500510353 25000000000000000000 500077288728019 500000000000000 1024 4727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500077288728019/500000000000000 : ℝ)) (X := (25017841750500510353/25000000000000000000 : ℝ)) (by norm_num) 4727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(372347380825251/25000000000000000000 : ℝ) ≤ ((6364088630414454409/6365000000000000000 : ℝ)+2*(105803332397/127300000000000 : ℝ)*(4501/50000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (6364088630414454409/6365000000000000000 : ℝ)+2*(105803332397/127300000000000 : ℝ)*(4501/50000 : ℝ)=(5000032263953411/5000000000000000 : ℝ) by norm_num, show 1+2*(372347380825251/25000000000000000000 : ℝ)=(12500372347380825251/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17841750500510353/50000000000000000000 : ℝ)+(372347380825251/25000000000000000000 : ℝ) ≤ ((6364088630414454409/6365000000000000000 : ℝ)+(105803332397/127300000000000 : ℝ)*((17913/100000 : ℝ)+(4501/50000 : ℝ)))^(4727/1024 : ℝ) := by
    rw [show (6364088630414454409/6365000000000000000 : ℝ)+(105803332397/127300000000000 : ℝ)*((17913/100000 : ℝ)+(4501/50000 : ℝ))=(10000805151233601/10000000000000000 : ℝ) by norm_num, show 1+(17841750500510353/50000000000000000000 : ℝ)+(372347380825251/25000000000000000000 : ℝ)=(10003717289052432171/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17841750500510353/50000000000000000000 : ℝ) ≤ ((6364088630414454409/6365000000000000000 : ℝ)+2*(105803332397/127300000000000 : ℝ)*(17913/100000 : ℝ))^(4727/1024 : ℝ) := by
    rw [show (6364088630414454409/6365000000000000000 : ℝ)+2*(105803332397/127300000000000 : ℝ)*(17913/100000 : ℝ)=(500077288728019/500000000000000 : ℝ) by norm_num, show 1+2*(17841750500510353/50000000000000000000 : ℝ)=(25017841750500510353/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6364088630414454409/6365000000000000000 : ℝ)*(X 1 0+X 2 0)+(105803332397/127300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (4501/50000 : ℝ)) (hi := (17913/100000 : ℝ)) (c := (6364088630414454409/6365000000000000000 : ℝ)) (alpha := (105803332397/127300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6364088630414454409/6365000000000000000 : ℝ)*(X 0 1+X 2 1)+(105803332397/127300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (4501/50000 : ℝ)) (hi := (17913/100000 : ℝ)) (c := (6364088630414454409/6365000000000000000 : ℝ)) (alpha := (105803332397/127300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6364088630414454409/6365000000000000000 : ℝ)*(X 0 2+X 1 2)+(105803332397/127300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4727/1024 : ℝ)) (lo := (4501/50000 : ℝ)) (hi := (17913/100000 : ℝ)) (c := (6364088630414454409/6365000000000000000 : ℝ)) (alpha := (105803332397/127300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1720418241/10000000000 : ℝ)*X 0 0+(34186307/62500000 : ℝ)*X 0 1+(5172985133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356725059/10000000000 : ℝ)*X 1 0+(-936888963/5000000000 : ℝ)*X 1 1+(129324629/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356725087/10000000000 : ℝ)*X 2 0+(5172985121/10000000000 : ℝ)*X 2 1+(-93688897/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4217260579/10000000000 : ℝ)*X 0 0+(3867967147/10000000000 : ℝ)*X 0 1+(1147661621/2500000000 : ℝ)*X 0 2+(4217260579/10000000000 : ℝ)*X 1 0+(3867967147/10000000000 : ℝ)*X 1 1+(1147661621/2500000000 : ℝ)*X 1 2+(4217260579/10000000000 : ℝ)*X 2 0+(3867967147/10000000000 : ℝ)*X 2 1+(1147661621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1720501741/10000000000 : ℝ)*X 0 0+(1293825707/2500000000 : ℝ)*X 0 1+(5467465929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055596979/2000000000 : ℝ)*X 1 0+(-98706071/625000000 : ℝ)*X 1 1+(218698643/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055597063/2000000000 : ℝ)*X 2 0+(42714573/78125000 : ℝ)*X 2 1+(-1579297583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((527183043/1250000000 : ℝ)*X 0 0+(917000711/2000000000 : ℝ)*X 0 1+(3873672639/10000000000 : ℝ)*X 0 2+(527183043/1250000000 : ℝ)*X 1 0+(917000711/2000000000 : ℝ)*X 1 1+(3873672639/10000000000 : ℝ)*X 1 2+(527183043/1250000000 : ℝ)*X 2 0+(917000711/2000000000 : ℝ)*X 2 1+(3873672639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1603_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1795910000700965792548431987/159125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192042781/10000000000000 : ℝ)*(base19) + (1818564227/100000000000000 : ℝ)*(base23) + (63998841/100000000000000 : ℝ)*(lower2) + (145616873/50000000000000 : ℝ)*(upper3) + (24168507/12500000000000 : ℝ)*(upper5) + (2376401555797119/100000000000000 : ℝ)*(major0) + (2376401555797119/100000000000000 : ℝ)*(major1) + (2376401555797119/100000000000000 : ℝ)*(major2) + (3369022711680149/100000000000000 : ℝ)*(sp0) + (421130336164951/12500000000000 : ℝ)*(sp1) + (421130348897899/12500000000000 : ℝ)*(sp2) + (138374826125769/10000000000000 : ℝ)*(sp3) + (2189806727/10000000000000 : ℝ)*(sp4) + (9864383831/100000000000000 : ℝ)*(sp7) + (691879062820761/50000000000000 : ℝ)*(f.failure) + (1684522304873709/50000000000000 : ℝ)*(f.sum) + (5928458416267/1591250000000000000000000000 : ℝ)*base65 + (2935793826046302329/636500000000000000000000000000000 : ℝ)*base68 + (3455810256607197671/636500000000000000000000000000000 : ℝ)*base69 + (3673333730612197671/636500000000000000000000000000000 : ℝ)*base71 + (4109699116653/1591250000000000000000000000 : ℝ)*base74 + (5506773251702697671/636500000000000000000000000000000 : ℝ)*base75 + (2931505181044197671/636500000000000000000000000000000 : ℝ)*base77 + (1829753094345697671/636500000000000000000000000000000 : ℝ)*base79 + (24638256623379/3182500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1423269/156250000000000000000 : ℝ)*base89 + (1423269/156250000000000000000 : ℝ)*base91 + (1423269/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24691592692667479509417/6365000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70537861/25000000000000 : ℝ)*(base19) + (8262293/1250000000000 : ℝ)*(base23) + (944173/12500000000000 : ℝ)*(upper3) + (10893169/12500000000000 : ℝ)*(lower4) + (14184833/20000000000000 : ℝ)*(upper5) + (603570202392083/25000000000000 : ℝ)*(major0) + (603570202392083/25000000000000 : ℝ)*(major1) + (603570202392083/25000000000000 : ℝ)*(major2) + (5783220833/100000000000000 : ℝ)*(sp1) + (463026773/25000000000000 : ℝ)*(sp2) + (213921662592791/6250000000000 : ℝ)*(sp4) + (1711370268056189/50000000000000 : ℝ)*(sp5) + (855686022098531/25000000000000 : ℝ)*(sp6) + (702907444171397/50000000000000 : ℝ)*(sp7) + (702907444171397/50000000000000 : ℝ)*(f.failure) + (213921662592791/6250000000000 : ℝ)*(f.sum) + (1409085379449/1591250000000000000000000000 : ℝ)*base66 + (313234582571843947/159125000000000000000000000000000 : ℝ)*base67 + (766899385665156053/159125000000000000000000000000000 : ℝ)*base70 + (470930514192531053/159125000000000000000000000000000 : ℝ)*base72 + (4591836836961/1591250000000000000000000000 : ℝ)*base73 + (1187453304430093947/159125000000000000000000000000000 : ℝ)*base75 + (624139502406406053/159125000000000000000000000000000 : ℝ)*base78 + (981176151789343947/159125000000000000000000000000000 : ℝ)*base79 + (3350633414503/3182500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1499587/156250000000000000000 : ℝ)*base90 + (1499587/156250000000000000000 : ℝ)*base92 + (1499587/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1603_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5117/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4131/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1603_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1603_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5117/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4131/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1603_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1603_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1603_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4727/1024 : ℝ) ≤ p) (hpb : p ≤ (4731/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5366729/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5117/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4131/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1603_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
