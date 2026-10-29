-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1326_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:45:30.345319+00:00
-- url     : https://prove2.me/submissions/23a23e7f-442f-4756-b494-51dbb334b48f

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
theorem support_rectangle_w1326_s3_0 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055942413/10000000000 : ℝ)*x 0 + (678658547/1250000000 : ℝ)*x 1 + (5229635833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055942413/10000000000 : ℝ)^2143 ≤ (1564093955519/12500000000000 : ℝ)^1631 := by
    have hnat : (2055942413 : ℕ)^2143*12500000000000^1631 ≤ 1564093955519^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055942413 10000000000 1564093955519 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678658547/1250000000 : ℝ)^2143 ≤ (896400045903/2000000000000 : ℝ)^1631 := by
    have hnat : (678658547 : ℕ)^2143*2000000000000^1631 ≤ 896400045903^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678658547 1250000000 896400045903 2000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229635833/10000000000 : ℝ)^2143 ≤ (42667246037317/100000000000000 : ℝ)^1631 := by
    have hnat : (5229635833 : ℕ)^2143*100000000000000^1631 ≤ 42667246037317^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229635833 10000000000 42667246037317 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055942413/10000000000 : ℝ), (678658547/1250000000 : ℝ), (5229635833/10000000000 : ℝ)] ![(1564093955519/12500000000000 : ℝ), (896400045903/2000000000000 : ℝ), (42667246037317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055942413/10000000000 : ℝ)|^2143 ≤ (1564093955519/12500000000000 : ℝ)^1631
        have hw : |(-2055942413/10000000000 : ℝ)|=(2055942413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678658547/1250000000 : ℝ)|^2143 ≤ (896400045903/2000000000000 : ℝ)^1631
        have hw : |(678658547/1250000000 : ℝ)|=(678658547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229635833/10000000000 : ℝ)|^2143 ≤ (42667246037317/100000000000000 : ℝ)^1631
        have hw : |(5229635833/10000000000 : ℝ)|=(5229635833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_1 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353270591/10000000000 : ℝ)*x 0 + (-1079006317/5000000000 : ℝ)*x 1 + (5229635571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353270591/10000000000 : ℝ)^2143 ≤ (10999372972449/25000000000000 : ℝ)^1631 := by
    have hnat : (5353270591 : ℕ)^2143*25000000000000^1631 ≤ 10999372972449^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353270591 10000000000 10999372972449 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079006317/5000000000 : ℝ)^2143 ≤ (13335264877221/100000000000000 : ℝ)^1631 := by
    have hnat : (1079006317 : ℕ)^2143*100000000000000^1631 ≤ 13335264877221^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079006317 5000000000 13335264877221 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229635571/10000000000 : ℝ)^2143 ≤ (426672432287/1000000000000 : ℝ)^1631 := by
    have hnat : (5229635571 : ℕ)^2143*1000000000000^1631 ≤ 426672432287^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229635571 10000000000 426672432287 1000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353270591/10000000000 : ℝ), (-1079006317/5000000000 : ℝ), (5229635571/10000000000 : ℝ)] ![(10999372972449/25000000000000 : ℝ), (13335264877221/100000000000000 : ℝ), (426672432287/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353270591/10000000000 : ℝ)|^2143 ≤ (10999372972449/25000000000000 : ℝ)^1631
        have hw : |(5353270591/10000000000 : ℝ)|=(5353270591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079006317/5000000000 : ℝ)|^2143 ≤ (13335264877221/100000000000000 : ℝ)^1631
        have hw : |(-1079006317/5000000000 : ℝ)|=(1079006317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229635571/10000000000 : ℝ)|^2143 ≤ (426672432287/1000000000000 : ℝ)^1631
        have hw : |(5229635571/10000000000 : ℝ)|=(5229635571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_2 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676635439/5000000000 : ℝ)*x 0 + (261481763/500000000 : ℝ)*x 1 + (-2158012663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676635439/5000000000 : ℝ)^2143 ≤ (21998747494531/50000000000000 : ℝ)^1631 := by
    have hnat : (2676635439 : ℕ)^2143*50000000000000^1631 ≤ 21998747494531^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676635439 5000000000 21998747494531 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261481763/500000000 : ℝ)^2143 ≤ (21333619947403/50000000000000 : ℝ)^1631 := by
    have hnat : (261481763 : ℕ)^2143*50000000000000^1631 ≤ 21333619947403^1631*500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261481763 500000000 21333619947403 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158012663/10000000000 : ℝ)^2143 ≤ (13335265112679/100000000000000 : ℝ)^1631 := by
    have hnat : (2158012663 : ℕ)^2143*100000000000000^1631 ≤ 13335265112679^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158012663 10000000000 13335265112679 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676635439/5000000000 : ℝ), (261481763/500000000 : ℝ), (-2158012663/10000000000 : ℝ)] ![(21998747494531/50000000000000 : ℝ), (21333619947403/50000000000000 : ℝ), (13335265112679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676635439/5000000000 : ℝ)|^2143 ≤ (21998747494531/50000000000000 : ℝ)^1631
        have hw : |(2676635439/5000000000 : ℝ)|=(2676635439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261481763/500000000 : ℝ)|^2143 ≤ (21333619947403/50000000000000 : ℝ)^1631
        have hw : |(261481763/500000000 : ℝ)|=(261481763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2158012663/10000000000 : ℝ)|^2143 ≤ (13335265112679/100000000000000 : ℝ)^1631
        have hw : |(-2158012663/10000000000 : ℝ)|=(2158012663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_3 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2164826899/5000000000 : ℝ)*x 0 + (4126530607/10000000000 : ℝ)*x 1 + (4542159709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164826899/5000000000 : ℝ)^2143 ≤ (6658238245557/20000000000000 : ℝ)^1631 := by
    have hnat : (2164826899 : ℕ)^2143*20000000000000^1631 ≤ 6658238245557^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164826899 5000000000 6658238245557 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126530607/10000000000 : ℝ)^2143 ≤ (3125434240289/10000000000000 : ℝ)^1631 := by
    have hnat : (4126530607 : ℕ)^2143*10000000000000^1631 ≤ 3125434240289^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126530607 10000000000 3125434240289 10000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542159709/10000000000 : ℝ)^2143 ≤ (17727233182199/50000000000000 : ℝ)^1631 := by
    have hnat : (4542159709 : ℕ)^2143*50000000000000^1631 ≤ 17727233182199^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542159709 10000000000 17727233182199 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164826899/5000000000 : ℝ), (4126530607/10000000000 : ℝ), (4542159709/10000000000 : ℝ)] ![(6658238245557/20000000000000 : ℝ), (3125434240289/10000000000000 : ℝ), (17727233182199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164826899/5000000000 : ℝ)|^2143 ≤ (6658238245557/20000000000000 : ℝ)^1631
        have hw : |(2164826899/5000000000 : ℝ)|=(2164826899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126530607/10000000000 : ℝ)|^2143 ≤ (3125434240289/10000000000000 : ℝ)^1631
        have hw : |(4126530607/10000000000 : ℝ)|=(4126530607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542159709/10000000000 : ℝ)|^2143 ≤ (17727233182199/50000000000000 : ℝ)^1631
        have hw : |(4542159709/10000000000 : ℝ)|=(4542159709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_4 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027981473/5000000000 : ℝ)*x 0 + (5230475703/10000000000 : ℝ)*x 1 + (5428423147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027981473/5000000000 : ℝ)^2143 ≤ (625645792019/5000000000000 : ℝ)^1631 := by
    have hnat : (1027981473 : ℕ)^2143*5000000000000^1631 ≤ 625645792019^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027981473 5000000000 625645792019 5000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230475703/10000000000 : ℝ)^2143 ≤ (10669062399987/25000000000000 : ℝ)^1631 := by
    have hnat : (5230475703 : ℕ)^2143*25000000000000^1631 ≤ 10669062399987^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230475703 10000000000 10669062399987 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428423147/10000000000 : ℝ)^2143 ≤ (8962166909919/20000000000000 : ℝ)^1631 := by
    have hnat : (5428423147 : ℕ)^2143*20000000000000^1631 ≤ 8962166909919^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428423147 10000000000 8962166909919 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027981473/5000000000 : ℝ), (5230475703/10000000000 : ℝ), (5428423147/10000000000 : ℝ)] ![(625645792019/5000000000000 : ℝ), (10669062399987/25000000000000 : ℝ), (8962166909919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027981473/5000000000 : ℝ)|^2143 ≤ (625645792019/5000000000000 : ℝ)^1631
        have hw : |(-1027981473/5000000000 : ℝ)|=(1027981473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230475703/10000000000 : ℝ)|^2143 ≤ (10669062399987/25000000000000 : ℝ)^1631
        have hw : |(5230475703/10000000000 : ℝ)|=(5230475703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428423147/10000000000 : ℝ)|^2143 ≤ (8962166909919/20000000000000 : ℝ)^1631
        have hw : |(5428423147/10000000000 : ℝ)|=(5428423147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_5 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530194347/1000000000 : ℝ)*x 0 + (-391845059/2000000000 : ℝ)*x 1 + (2714211673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530194347/1000000000 : ℝ)^2143 ≤ (8688810943351/20000000000000 : ℝ)^1631 := by
    have hnat : (530194347 : ℕ)^2143*20000000000000^1631 ≤ 8688810943351^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530194347 1000000000 8688810943351 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391845059/2000000000 : ℝ)^2143 ≤ (5872554280321/50000000000000 : ℝ)^1631 := by
    have hnat : (391845059 : ℕ)^2143*50000000000000^1631 ≤ 5872554280321^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391845059 2000000000 5872554280321 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714211673/5000000000 : ℝ)^2143 ≤ (44810836707989/100000000000000 : ℝ)^1631 := by
    have hnat : (2714211673 : ℕ)^2143*100000000000000^1631 ≤ 44810836707989^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714211673 5000000000 44810836707989 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530194347/1000000000 : ℝ), (-391845059/2000000000 : ℝ), (2714211673/5000000000 : ℝ)] ![(8688810943351/20000000000000 : ℝ), (5872554280321/50000000000000 : ℝ), (44810836707989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530194347/1000000000 : ℝ)|^2143 ≤ (8688810943351/20000000000000 : ℝ)^1631
        have hw : |(530194347/1000000000 : ℝ)|=(530194347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391845059/2000000000 : ℝ)|^2143 ≤ (5872554280321/50000000000000 : ℝ)^1631
        have hw : |(-391845059/2000000000 : ℝ)|=(391845059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714211673/5000000000 : ℝ)|^2143 ≤ (44810836707989/100000000000000 : ℝ)^1631
        have hw : |(2714211673/5000000000 : ℝ)|=(2714211673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_6 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662743147/1250000000 : ℝ)*x 0 + (108568443/200000000 : ℝ)*x 1 + (-195922461/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662743147/1250000000 : ℝ)^2143 ≤ (1357627283873/3125000000000 : ℝ)^1631 := by
    have hnat : (662743147 : ℕ)^2143*3125000000000^1631 ≤ 1357627283873^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662743147 1250000000 1357627283873 3125000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108568443/200000000 : ℝ)^2143 ≤ (350084560437/781250000000 : ℝ)^1631 := by
    have hnat : (108568443 : ℕ)^2143*781250000000^1631 ≤ 350084560437^1631*200000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108568443 200000000 350084560437 781250000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195922461/1000000000 : ℝ)^2143 ≤ (5872551582573/50000000000000 : ℝ)^1631 := by
    have hnat : (195922461 : ℕ)^2143*50000000000000^1631 ≤ 5872551582573^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195922461 1000000000 5872551582573 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662743147/1250000000 : ℝ), (108568443/200000000 : ℝ), (-195922461/1000000000 : ℝ)] ![(1357627283873/3125000000000 : ℝ), (350084560437/781250000000 : ℝ), (5872551582573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662743147/1250000000 : ℝ)|^2143 ≤ (1357627283873/3125000000000 : ℝ)^1631
        have hw : |(662743147/1250000000 : ℝ)|=(662743147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108568443/200000000 : ℝ)|^2143 ≤ (350084560437/781250000000 : ℝ)^1631
        have hw : |(108568443/200000000 : ℝ)|=(108568443/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195922461/1000000000 : ℝ)|^2143 ≤ (5872551582573/50000000000000 : ℝ)^1631
        have hw : |(-195922461/1000000000 : ℝ)|=(195922461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s3_7 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4329696117/10000000000 : ℝ)*x 0 + (2270205517/5000000000 : ℝ)*x 1 + (4128289573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329696117/10000000000 : ℝ)^2143 ≤ (8322904692853/25000000000000 : ℝ)^1631 := by
    have hnat : (4329696117 : ℕ)^2143*25000000000000^1631 ≤ 8322904692853^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329696117 10000000000 8322904692853 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270205517/5000000000 : ℝ)^2143 ≤ (138423957379/390625000000 : ℝ)^1631 := by
    have hnat : (2270205517 : ℕ)^2143*390625000000^1631 ≤ 138423957379^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270205517 5000000000 138423957379 390625000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128289573/10000000000 : ℝ)^2143 ≤ (1954490507743/6250000000000 : ℝ)^1631 := by
    have hnat : (4128289573 : ℕ)^2143*6250000000000^1631 ≤ 1954490507743^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128289573 10000000000 1954490507743 6250000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329696117/10000000000 : ℝ), (2270205517/5000000000 : ℝ), (4128289573/10000000000 : ℝ)] ![(8322904692853/25000000000000 : ℝ), (138423957379/390625000000 : ℝ), (1954490507743/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329696117/10000000000 : ℝ)|^2143 ≤ (8322904692853/25000000000000 : ℝ)^1631
        have hw : |(4329696117/10000000000 : ℝ)|=(4329696117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270205517/5000000000 : ℝ)|^2143 ≤ (138423957379/390625000000 : ℝ)^1631
        have hw : |(2270205517/5000000000 : ℝ)|=(2270205517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128289573/10000000000 : ℝ)|^2143 ≤ (1954490507743/6250000000000 : ℝ)^1631
        have hw : |(4128289573/10000000000 : ℝ)|=(4128289573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1326_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5401/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7513/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1949/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1949/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1949/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1949/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1949/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1949/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1949/20000 : ℝ) ^ (4285/1024 : ℝ) ≤ (2933975797392369/50000000000000000000 : ℝ) := by
    have hpowers : (1949/20000 : ℝ)^4285 ≤ (2933975797392369/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1949 : ℕ)^4285*50000000000000000000^1024 ≤ 2933975797392369^1024*20000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1949 20000 2933975797392369 50000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1949/20000 : ℝ)) (X := (2933975797392369/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16169/100000 : ℝ) ^ (4285/1024 : ℝ) ≤ (48829136911143891/100000000000000000000 : ℝ) := by
    have hpowers : (16169/100000 : ℝ)^4285 ≤ (48829136911143891/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16169 : ℕ)^4285*100000000000000000000^1024 ≤ 48829136911143891^1024*100000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16169 100000 48829136911143891 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16169/100000 : ℝ)) (X := (48829136911143891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002933975797392369/25000000000000000000 : ℝ) ≤ (5000140222033121/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (25002933975797392369/25000000000000000000 : ℝ)^1024 ≤ (5000140222033121/5000000000000000 : ℝ)^4285 := by
      have hnat : (25002933975797392369 : ℕ)^1024*5000000000000000^4285 ≤ 5000140222033121^4285*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002933975797392369 25000000000000000000 5000140222033121 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140222033121/5000000000000000 : ℝ)) (X := (25002933975797392369/25000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054697088505928629/100000000000000000000 : ℝ) ≤ (80010454733267/80000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (100054697088505928629/100000000000000000000 : ℝ)^1024 ≤ (80010454733267/80000000000000 : ℝ)^4285 := by
      have hnat : (100054697088505928629 : ℕ)^1024*80000000000000^4285 ≤ 80010454733267^4285*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054697088505928629 100000000000000000000 80010454733267 80000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80010454733267/80000000000000 : ℝ)) (X := (100054697088505928629/100000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048829136911143891/50000000000000000000 : ℝ) ≤ (2500583309812627/2500000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (50048829136911143891/50000000000000000000 : ℝ)^1024 ≤ (2500583309812627/2500000000000000 : ℝ)^4285 := by
      have hnat : (50048829136911143891 : ℕ)^1024*2500000000000000^4285 ≤ 2500583309812627^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048829136911143891 50000000000000000000 2500583309812627 2500000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500583309812627/2500000000000000 : ℝ)) (X := (50048829136911143891/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2933975797392369/50000000000000000000 : ℝ) ≤ ((32110898541805433219/32120000000000000000 : ℝ)+2*(1026397592133/642400000000000 : ℝ)*(1949/20000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (32110898541805433219/32120000000000000000 : ℝ)+2*(1026397592133/642400000000000 : ℝ)*(1949/20000 : ℝ)=(5000140222033121/5000000000000000 : ℝ) by norm_num, show 1+2*(2933975797392369/50000000000000000000 : ℝ)=(25002933975797392369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48829136911143891/100000000000000000000 : ℝ)+(2933975797392369/50000000000000000000 : ℝ) ≤ ((32110898541805433219/32120000000000000000 : ℝ)+(1026397592133/642400000000000 : ℝ)*((16169/100000 : ℝ)+(1949/20000 : ℝ)))^(4285/1024 : ℝ) := by
    rw [show (32110898541805433219/32120000000000000000 : ℝ)+(1026397592133/642400000000000 : ℝ)*((16169/100000 : ℝ)+(1949/20000 : ℝ))=(80010454733267/80000000000000 : ℝ) by norm_num, show 1+(48829136911143891/100000000000000000000 : ℝ)+(2933975797392369/50000000000000000000 : ℝ)=(100054697088505928629/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48829136911143891/100000000000000000000 : ℝ) ≤ ((32110898541805433219/32120000000000000000 : ℝ)+2*(1026397592133/642400000000000 : ℝ)*(16169/100000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (32110898541805433219/32120000000000000000 : ℝ)+2*(1026397592133/642400000000000 : ℝ)*(16169/100000 : ℝ)=(2500583309812627/2500000000000000 : ℝ) by norm_num, show 1+2*(48829136911143891/100000000000000000000 : ℝ)=(50048829136911143891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32110898541805433219/32120000000000000000 : ℝ)*(X 1 0+X 2 0)+(1026397592133/642400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (1949/20000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (32110898541805433219/32120000000000000000 : ℝ)) (alpha := (1026397592133/642400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32110898541805433219/32120000000000000000 : ℝ)*(X 0 1+X 2 1)+(1026397592133/642400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (1949/20000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (32110898541805433219/32120000000000000000 : ℝ)) (alpha := (1026397592133/642400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32110898541805433219/32120000000000000000 : ℝ)*(X 0 2+X 1 2)+(1026397592133/642400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (1949/20000 : ℝ)) (hi := (16169/100000 : ℝ)) (c := (32110898541805433219/32120000000000000000 : ℝ)) (alpha := (1026397592133/642400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2055942413/10000000000 : ℝ)*X 0 0+(678658547/1250000000 : ℝ)*X 0 1+(5229635833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353270591/10000000000 : ℝ)*X 1 0+(-1079006317/5000000000 : ℝ)*X 1 1+(5229635571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676635439/5000000000 : ℝ)*X 2 0+(261481763/500000000 : ℝ)*X 2 1+(-2158012663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2164826899/5000000000 : ℝ)*X 0 0+(4126530607/10000000000 : ℝ)*X 0 1+(4542159709/10000000000 : ℝ)*X 0 2+(2164826899/5000000000 : ℝ)*X 1 0+(4126530607/10000000000 : ℝ)*X 1 1+(4542159709/10000000000 : ℝ)*X 1 2+(2164826899/5000000000 : ℝ)*X 2 0+(4126530607/10000000000 : ℝ)*X 2 1+(4542159709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1027981473/5000000000 : ℝ)*X 0 0+(5230475703/10000000000 : ℝ)*X 0 1+(5428423147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530194347/1000000000 : ℝ)*X 1 0+(-391845059/2000000000 : ℝ)*X 1 1+(2714211673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662743147/1250000000 : ℝ)*X 2 0+(108568443/200000000 : ℝ)*X 2 1+(-195922461/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4329696117/10000000000 : ℝ)*X 0 0+(2270205517/5000000000 : ℝ)*X 0 1+(4128289573/10000000000 : ℝ)*X 0 2+(4329696117/10000000000 : ℝ)*X 1 0+(2270205517/5000000000 : ℝ)*X 1 1+(4128289573/10000000000 : ℝ)*X 1 2+(4329696117/10000000000 : ℝ)*X 2 0+(2270205517/5000000000 : ℝ)*X 2 1+(4128289573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2212519778310706822135772469/803000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320991341/50000000000000 : ℝ)*(base19) + (733023851/100000000000000 : ℝ)*(base23) + (2090719/1562500000000 : ℝ)*(lower2) + (116873127/100000000000000 : ℝ)*(upper3) + (1211829/3125000000000 : ℝ)*(lower4) + (1853801069308083/50000000000000 : ℝ)*(major0) + (1853801069308083/50000000000000 : ℝ)*(major1) + (1853801069308083/50000000000000 : ℝ)*(major2) + (156537701880659/3125000000000 : ℝ)*(sp0) + (5009208742666803/100000000000000 : ℝ)*(sp1) + (2504604325812817/50000000000000 : ℝ)*(sp2) + (2405991565005711/100000000000000 : ℝ)*(sp3) + (2924468397/100000000000000 : ℝ)*(sp4) + (3235733223/100000000000000 : ℝ)*(sp7) + (1202997400369467/50000000000000 : ℝ)*(f.failure) + (1001841876929897/20000000000000 : ℝ)*(f.sum) + (95286614850741/16060000000000000000000000000 : ℝ)*base66 + (7382337857117359177/1606000000000000000000000000000000 : ℝ)*base67 + (3502108233099359177/1606000000000000000000000000000000 : ℝ)*base69 + (4321572963506640823/1606000000000000000000000000000000 : ℝ)*base72 + (12309643795619/16060000000000000000000000000 : ℝ)*base73 + (2843419154000640823/1606000000000000000000000000000000 : ℝ)*base76 + (11034041733619359177/1606000000000000000000000000000000 : ℝ)*base77 + (2765531657551359177/1606000000000000000000000000000000 : ℝ)*base79 + (100717239177121/16060000000000000000000000000 : ℝ)*base82 + (1419417/500000000000000000000 : ℝ)*base89 + (1419417/500000000000000000000 : ℝ)*base91 + (1419417/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26527462124516469408597/4015000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1655655683/100000000000000 : ℝ)*(base19) + (94119781/2500000000000 : ℝ)*(base23) + (349437807/100000000000000 : ℝ)*(upper3) + (95921079/100000000000000 : ℝ)*(lower4) + (47627867/25000000000000 : ℝ)*(upper5) + (467395481872373/12500000000000 : ℝ)*(major0) + (467395481872373/12500000000000 : ℝ)*(major1) + (467395481872373/12500000000000 : ℝ)*(major2) + (25554374179/100000000000000 : ℝ)*(sp1) + (56823138643/100000000000000 : ℝ)*(sp2) + (1010370233898109/20000000000000 : ℝ)*(sp4) + (5051823959460683/100000000000000 : ℝ)*(sp5) + (2525895290780331/50000000000000 : ℝ)*(sp6) + (30330954002889/1250000000000 : ℝ)*(sp7) + (30330954002889/1250000000000 : ℝ)*(f.failure) + (1010370233898109/20000000000000 : ℝ)*(f.sum) + (8648085270441/4015000000000000000000000000 : ℝ)*base66 + (1036519338709491313/401500000000000000000000000000000 : ℝ)*base68 + (2919279221300508687/401500000000000000000000000000000 : ℝ)*base69 + (1261365210245491313/401500000000000000000000000000000 : ℝ)*base72 + (14666699978013/2007500000000000000000000000 : ℝ)*base74 + (4672637184382508687/401500000000000000000000000000000 : ℝ)*base75 + (1241366865054008687/401500000000000000000000000000000 : ℝ)*base77 + (1020494407726991313/401500000000000000000000000000000 : ℝ)*base80 + (1498642820393/501875000000000000000000000 : ℝ)*base81 + (59539/12500000000000000000 : ℝ)*base89 + (59539/12500000000000000000 : ℝ)*base91 + (59539/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1326_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7513/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1326_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1326_s4_0 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057535817/10000000000 : ℝ)*x 0 + (6770501/12500000 : ℝ)*x 1 + (2620728911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057535817/10000000000 : ℝ)^2143 ≤ (3131373786673/25000000000000 : ℝ)^1631 := by
    have hnat : (2057535817 : ℕ)^2143*25000000000000^1631 ≤ 3131373786673^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057535817 10000000000 3131373786673 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6770501/12500000 : ℝ)^2143 ≤ (44680483138707/100000000000000 : ℝ)^1631 := by
    have hnat : (6770501 : ℕ)^2143*100000000000000^1631 ≤ 44680483138707^1631*12500000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6770501 12500000 44680483138707 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620728911/5000000000 : ℝ)^2143 ≤ (5349252713391/12500000000000 : ℝ)^1631 := by
    have hnat : (2620728911 : ℕ)^2143*12500000000000^1631 ≤ 5349252713391^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620728911 5000000000 5349252713391 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057535817/10000000000 : ℝ), (6770501/12500000 : ℝ), (2620728911/5000000000 : ℝ)] ![(3131373786673/25000000000000 : ℝ), (44680483138707/100000000000000 : ℝ), (5349252713391/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057535817/10000000000 : ℝ)|^2143 ≤ (3131373786673/25000000000000 : ℝ)^1631
        have hw : |(-2057535817/10000000000 : ℝ)|=(2057535817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6770501/12500000 : ℝ)|^2143 ≤ (44680483138707/100000000000000 : ℝ)^1631
        have hw : |(6770501/12500000 : ℝ)|=(6770501/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620728911/5000000000 : ℝ)|^2143 ≤ (5349252713391/12500000000000 : ℝ)^1631
        have hw : |(2620728911/5000000000 : ℝ)|=(2620728911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_1 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350000149/10000000000 : ℝ)*x 0 + (-1073369179/5000000000 : ℝ)*x 1 + (5241457691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350000149/10000000000 : ℝ)^2143 ≤ (43962178310977/100000000000000 : ℝ)^1631 := by
    have hnat : (5350000149 : ℕ)^2143*100000000000000^1631 ≤ 43962178310977^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350000149 10000000000 43962178310977 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073369179/5000000000 : ℝ)^2143 ≤ (13243801373091/100000000000000 : ℝ)^1631 := by
    have hnat : (1073369179 : ℕ)^2143*100000000000000^1631 ≤ 13243801373091^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073369179 5000000000 13243801373091 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241457691/10000000000 : ℝ)^2143 ≤ (41791035451/97656250000 : ℝ)^1631 := by
    have hnat : (5241457691 : ℕ)^2143*97656250000^1631 ≤ 41791035451^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241457691 10000000000 41791035451 97656250000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350000149/10000000000 : ℝ), (-1073369179/5000000000 : ℝ), (5241457691/10000000000 : ℝ)] ![(43962178310977/100000000000000 : ℝ), (13243801373091/100000000000000 : ℝ), (41791035451/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350000149/10000000000 : ℝ)|^2143 ≤ (43962178310977/100000000000000 : ℝ)^1631
        have hw : |(5350000149/10000000000 : ℝ)|=(5350000149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073369179/5000000000 : ℝ)|^2143 ≤ (13243801373091/100000000000000 : ℝ)^1631
        have hw : |(-1073369179/5000000000 : ℝ)|=(1073369179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241457691/10000000000 : ℝ)|^2143 ≤ (41791035451/97656250000 : ℝ)^1631
        have hw : |(5241457691/10000000000 : ℝ)|=(5241457691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_2 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675000097/5000000000 : ℝ)*x 0 + (327591089/625000000 : ℝ)*x 1 + (-536684663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675000097/5000000000 : ℝ)^2143 ≤ (43962178796831/100000000000000 : ℝ)^1631 := by
    have hnat : (2675000097 : ℕ)^2143*100000000000000^1631 ≤ 43962178796831^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675000097 5000000000 43962178796831 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327591089/625000000 : ℝ)^2143 ≤ (42794017437577/100000000000000 : ℝ)^1631 := by
    have hnat : (327591089 : ℕ)^2143*100000000000000^1631 ≤ 42794017437577^1631*625000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327591089 625000000 42794017437577 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536684663/2500000000 : ℝ)^2143 ≤ (3310950939057/25000000000000 : ℝ)^1631 := by
    have hnat : (536684663 : ℕ)^2143*25000000000000^1631 ≤ 3310950939057^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536684663 2500000000 3310950939057 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675000097/5000000000 : ℝ), (327591089/625000000 : ℝ), (-536684663/2500000000 : ℝ)] ![(43962178796831/100000000000000 : ℝ), (42794017437577/100000000000000 : ℝ), (3310950939057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675000097/5000000000 : ℝ)|^2143 ≤ (43962178796831/100000000000000 : ℝ)^1631
        have hw : |(2675000097/5000000000 : ℝ)|=(2675000097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327591089/625000000 : ℝ)|^2143 ≤ (42794017437577/100000000000000 : ℝ)^1631
        have hw : |(327591089/625000000 : ℝ)|=(327591089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536684663/2500000000 : ℝ)|^2143 ≤ (3310950939057/25000000000000 : ℝ)^1631
        have hw : |(-536684663/2500000000 : ℝ)|=(536684663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_3 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (866124159/2000000000 : ℝ)*x 0 + (4152111433/10000000000 : ℝ)*x 1 + (4516338239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866124159/2000000000 : ℝ)^2143 ≤ (16650480503219/50000000000000 : ℝ)^1631 := by
    have hnat : (866124159 : ℕ)^2143*50000000000000^1631 ≤ 16650480503219^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866124159 2000000000 16650480503219 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152111433/10000000000 : ℝ)^2143 ≤ (1575458012361/5000000000000 : ℝ)^1631 := by
    have hnat : (4152111433 : ℕ)^2143*5000000000000^1631 ≤ 1575458012361^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152111433 10000000000 1575458012361 5000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516338239/10000000000 : ℝ)^2143 ≤ (35189878737287/100000000000000 : ℝ)^1631 := by
    have hnat : (4516338239 : ℕ)^2143*100000000000000^1631 ≤ 35189878737287^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516338239 10000000000 35189878737287 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866124159/2000000000 : ℝ), (4152111433/10000000000 : ℝ), (4516338239/10000000000 : ℝ)] ![(16650480503219/50000000000000 : ℝ), (1575458012361/5000000000000 : ℝ), (35189878737287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866124159/2000000000 : ℝ)|^2143 ≤ (16650480503219/50000000000000 : ℝ)^1631
        have hw : |(866124159/2000000000 : ℝ)|=(866124159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152111433/10000000000 : ℝ)|^2143 ≤ (1575458012361/5000000000000 : ℝ)^1631
        have hw : |(4152111433/10000000000 : ℝ)|=(4152111433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516338239/10000000000 : ℝ)|^2143 ≤ (35189878737287/100000000000000 : ℝ)^1631
        have hw : |(4516338239/10000000000 : ℝ)|=(4516338239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_4 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057549481/10000000000 : ℝ)*x 0 + (1048420681/2000000000 : ℝ)*x 1 + (338484483/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057549481/10000000000 : ℝ)^2143 ≤ (782850277507/6250000000000 : ℝ)^1631 := by
    have hnat : (2057549481 : ℕ)^2143*6250000000000^1631 ≤ 782850277507^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057549481 10000000000 782850277507 6250000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048420681/2000000000 : ℝ)^2143 ≤ (42800947343711/100000000000000 : ℝ)^1631 := by
    have hnat : (1048420681 : ℕ)^2143*100000000000000^1631 ≤ 42800947343711^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048420681 2000000000 42800947343711 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338484483/625000000 : ℝ)^2143 ≤ (4467344820543/10000000000000 : ℝ)^1631 := by
    have hnat : (338484483 : ℕ)^2143*10000000000000^1631 ≤ 4467344820543^1631*625000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338484483 625000000 4467344820543 10000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057549481/10000000000 : ℝ), (1048420681/2000000000 : ℝ), (338484483/625000000 : ℝ)] ![(782850277507/6250000000000 : ℝ), (42800947343711/100000000000000 : ℝ), (4467344820543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057549481/10000000000 : ℝ)|^2143 ≤ (782850277507/6250000000000 : ℝ)^1631
        have hw : |(-2057549481/10000000000 : ℝ)|=(2057549481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048420681/2000000000 : ℝ)|^2143 ≤ (42800947343711/100000000000000 : ℝ)^1631
        have hw : |(1048420681/2000000000 : ℝ)|=(1048420681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338484483/625000000 : ℝ)|^2143 ≤ (4467344820543/10000000000000 : ℝ)^1631
        have hw : |(338484483/625000000 : ℝ)|=(338484483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_5 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652511379/5000000000 : ℝ)*x 0 + (-1972444527/10000000000 : ℝ)*x 1 + (216630069/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652511379/5000000000 : ℝ)^2143 ≤ (43477210047267/100000000000000 : ℝ)^1631 := by
    have hnat : (2652511379 : ℕ)^2143*100000000000000^1631 ≤ 43477210047267^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652511379 5000000000 43477210047267 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972444527/10000000000 : ℝ)^2143 ≤ (11849341760619/100000000000000 : ℝ)^1631 := by
    have hnat : (1972444527 : ℕ)^2143*100000000000000^1631 ≤ 11849341760619^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972444527 10000000000 11849341760619 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216630069/400000000 : ℝ)^2143 ≤ (8934689634583/20000000000000 : ℝ)^1631 := by
    have hnat : (216630069 : ℕ)^2143*20000000000000^1631 ≤ 8934689634583^1631*400000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216630069 400000000 8934689634583 20000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652511379/5000000000 : ℝ), (-1972444527/10000000000 : ℝ), (216630069/400000000 : ℝ)] ![(43477210047267/100000000000000 : ℝ), (11849341760619/100000000000000 : ℝ), (8934689634583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652511379/5000000000 : ℝ)|^2143 ≤ (43477210047267/100000000000000 : ℝ)^1631
        have hw : |(2652511379/5000000000 : ℝ)|=(2652511379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972444527/10000000000 : ℝ)|^2143 ≤ (11849341760619/100000000000000 : ℝ)^1631
        have hw : |(-1972444527/10000000000 : ℝ)|=(1972444527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216630069/400000000 : ℝ)|^2143 ≤ (8934689634583/20000000000000 : ℝ)^1631
        have hw : |(216630069/400000000 : ℝ)|=(216630069/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_6 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652511387/5000000000 : ℝ)*x 0 + (1083150341/2000000000 : ℝ)*x 1 + (-1972444533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652511387/5000000000 : ℝ)^2143 ≤ (21738605109779/50000000000000 : ℝ)^1631 := by
    have hnat : (2652511387 : ℕ)^2143*50000000000000^1631 ≤ 21738605109779^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652511387 5000000000 21738605109779 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083150341/2000000000 : ℝ)^2143 ≤ (893468959123/2000000000000 : ℝ)^1631 := by
    have hnat : (1083150341 : ℕ)^2143*2000000000000^1631 ≤ 893468959123^1631*2000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083150341 2000000000 893468959123 2000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972444533/10000000000 : ℝ)^2143 ≤ (5924670903989/50000000000000 : ℝ)^1631 := by
    have hnat : (1972444533 : ℕ)^2143*50000000000000^1631 ≤ 5924670903989^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972444533 10000000000 5924670903989 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652511387/5000000000 : ℝ), (1083150341/2000000000 : ℝ), (-1972444533/10000000000 : ℝ)] ![(21738605109779/50000000000000 : ℝ), (893468959123/2000000000000 : ℝ), (5924670903989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652511387/5000000000 : ℝ)|^2143 ≤ (21738605109779/50000000000000 : ℝ)^1631
        have hw : |(2652511387/5000000000 : ℝ)|=(2652511387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083150341/2000000000 : ℝ)|^2143 ≤ (893468959123/2000000000000 : ℝ)^1631
        have hw : |(1083150341/2000000000 : ℝ)|=(1083150341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972444533/10000000000 : ℝ)|^2143 ≤ (5924670903989/50000000000000 : ℝ)^1631
        have hw : |(-1972444533/10000000000 : ℝ)|=(1972444533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s4_7 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4330649091/10000000000 : ℝ)*x 0 + (4514993711/10000000000 : ℝ)*x 1 + (4153463117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330649091/10000000000 : ℝ)^2143 ≤ (8325311724331/25000000000000 : ℝ)^1631 := by
    have hnat : (4330649091 : ℕ)^2143*25000000000000^1631 ≤ 8325311724331^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330649091 10000000000 8325311724331 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514993711/10000000000 : ℝ)^2143 ≤ (703522291949/2000000000000 : ℝ)^1631 := by
    have hnat : (4514993711 : ℕ)^2143*2000000000000^1631 ≤ 703522291949^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514993711 10000000000 703522291949 2000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153463117/10000000000 : ℝ)^2143 ≤ (3152263849389/10000000000000 : ℝ)^1631 := by
    have hnat : (4153463117 : ℕ)^2143*10000000000000^1631 ≤ 3152263849389^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153463117 10000000000 3152263849389 10000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330649091/10000000000 : ℝ), (4514993711/10000000000 : ℝ), (4153463117/10000000000 : ℝ)] ![(8325311724331/25000000000000 : ℝ), (703522291949/2000000000000 : ℝ), (3152263849389/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330649091/10000000000 : ℝ)|^2143 ≤ (8325311724331/25000000000000 : ℝ)^1631
        have hw : |(4330649091/10000000000 : ℝ)|=(4330649091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514993711/10000000000 : ℝ)|^2143 ≤ (703522291949/2000000000000 : ℝ)^1631
        have hw : |(4514993711/10000000000 : ℝ)|=(4514993711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153463117/10000000000 : ℝ)|^2143 ≤ (3152263849389/10000000000000 : ℝ)^1631
        have hw : |(4153463117/10000000000 : ℝ)|=(4153463117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1326_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7513/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5527/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7513/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7513/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7513/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7513/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7513/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7513/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5401/50000 : ℝ) ^ (4285/1024 : ℝ) ≤ (9028804615813517/100000000000000000000 : ℝ) := by
    have hpowers : (5401/50000 : ℝ)^4285 ≤ (9028804615813517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5401 : ℕ)^4285*100000000000000000000^1024 ≤ 9028804615813517^1024*50000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5401 50000 9028804615813517 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5401/50000 : ℝ)) (X := (9028804615813517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7513/50000 : ℝ) ^ (4285/1024 : ℝ) ≤ (35928845664867011/100000000000000000000 : ℝ) := by
    have hpowers : (7513/50000 : ℝ)^4285 ≤ (35928845664867011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7513 : ℕ)^4285*100000000000000000000^1024 ≤ 35928845664867011^1024*50000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7513 50000 35928845664867011 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7513/50000 : ℝ)) (X := (35928845664867011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009028804615813517/50000000000000000000 : ℝ) ≤ (10000431498750099/10000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (50009028804615813517/50000000000000000000 : ℝ)^1024 ≤ (10000431498750099/10000000000000000 : ℝ)^4285 := by
      have hnat : (50009028804615813517 : ℕ)^1024*10000000000000000^4285 ≤ 10000431498750099^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009028804615813517 50000000000000000000 10000431498750099 10000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000431498750099/10000000000000000 : ℝ)) (X := (50009028804615813517/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252809853142542533/6250000000000000000 : ℝ) ≤ (1250134272930231/1250000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (6252809853142542533/6250000000000000000 : ℝ)^1024 ≤ (1250134272930231/1250000000000000 : ℝ)^4285 := by
      have hnat : (6252809853142542533 : ℕ)^1024*1250000000000000^4285 ≤ 1250134272930231^4285*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252809853142542533 6250000000000000000 1250134272930231 1250000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250134272930231/1250000000000000 : ℝ)) (X := (6252809853142542533/6250000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035928845664867011/50000000000000000000 : ℝ) ≤ (10001716868133597/10000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (50035928845664867011/50000000000000000000 : ℝ)^1024 ≤ (10001716868133597/10000000000000000 : ℝ)^4285 := by
      have hnat : (50035928845664867011 : ℕ)^1024*10000000000000000^4285 ≤ 10001716868133597^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035928845664867011 50000000000000000000 10001716868133597 10000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001716868133597/10000000000000000 : ℝ)) (X := (50035928845664867011/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9028804615813517/100000000000000000000 : ℝ) ≤ ((63981724379757383/64000000000000000 : ℝ)+2*(214228230583/140800000000000 : ℝ)*(5401/50000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (63981724379757383/64000000000000000 : ℝ)+2*(214228230583/140800000000000 : ℝ)*(5401/50000 : ℝ)=(10000431498750099/10000000000000000 : ℝ) by norm_num, show 1+2*(9028804615813517/100000000000000000000 : ℝ)=(50009028804615813517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35928845664867011/100000000000000000000 : ℝ)+(9028804615813517/100000000000000000000 : ℝ) ≤ ((63981724379757383/64000000000000000 : ℝ)+(214228230583/140800000000000 : ℝ)*((7513/50000 : ℝ)+(5401/50000 : ℝ)))^(4285/1024 : ℝ) := by
    rw [show (63981724379757383/64000000000000000 : ℝ)+(214228230583/140800000000000 : ℝ)*((7513/50000 : ℝ)+(5401/50000 : ℝ))=(1250134272930231/1250000000000000 : ℝ) by norm_num, show 1+(35928845664867011/100000000000000000000 : ℝ)+(9028804615813517/100000000000000000000 : ℝ)=(6252809853142542533/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35928845664867011/100000000000000000000 : ℝ) ≤ ((63981724379757383/64000000000000000 : ℝ)+2*(214228230583/140800000000000 : ℝ)*(7513/50000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (63981724379757383/64000000000000000 : ℝ)+2*(214228230583/140800000000000 : ℝ)*(7513/50000 : ℝ)=(10001716868133597/10000000000000000 : ℝ) by norm_num, show 1+2*(35928845664867011/100000000000000000000 : ℝ)=(50035928845664867011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63981724379757383/64000000000000000 : ℝ)*(X 1 0+X 2 0)+(214228230583/140800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (5401/50000 : ℝ)) (hi := (7513/50000 : ℝ)) (c := (63981724379757383/64000000000000000 : ℝ)) (alpha := (214228230583/140800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63981724379757383/64000000000000000 : ℝ)*(X 0 1+X 2 1)+(214228230583/140800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (5401/50000 : ℝ)) (hi := (7513/50000 : ℝ)) (c := (63981724379757383/64000000000000000 : ℝ)) (alpha := (214228230583/140800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63981724379757383/64000000000000000 : ℝ)*(X 0 2+X 1 2)+(214228230583/140800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (5401/50000 : ℝ)) (hi := (7513/50000 : ℝ)) (c := (63981724379757383/64000000000000000 : ℝ)) (alpha := (214228230583/140800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2057535817/10000000000 : ℝ)*X 0 0+(6770501/12500000 : ℝ)*X 0 1+(2620728911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350000149/10000000000 : ℝ)*X 1 0+(-1073369179/5000000000 : ℝ)*X 1 1+(5241457691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675000097/5000000000 : ℝ)*X 2 0+(327591089/625000000 : ℝ)*X 2 1+(-536684663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866124159/2000000000 : ℝ)*X 0 0+(4152111433/10000000000 : ℝ)*X 0 1+(4516338239/10000000000 : ℝ)*X 0 2+(866124159/2000000000 : ℝ)*X 1 0+(4152111433/10000000000 : ℝ)*X 1 1+(4516338239/10000000000 : ℝ)*X 1 2+(866124159/2000000000 : ℝ)*X 2 0+(4152111433/10000000000 : ℝ)*X 2 1+(4516338239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2057549481/10000000000 : ℝ)*X 0 0+(1048420681/2000000000 : ℝ)*X 0 1+(338484483/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652511379/5000000000 : ℝ)*X 1 0+(-1972444527/10000000000 : ℝ)*X 1 1+(216630069/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652511387/5000000000 : ℝ)*X 2 0+(1083150341/2000000000 : ℝ)*X 2 1+(-1972444533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330649091/10000000000 : ℝ)*X 0 0+(4514993711/10000000000 : ℝ)*X 0 1+(4153463117/10000000000 : ℝ)*X 0 2+(4330649091/10000000000 : ℝ)*X 1 0+(4514993711/10000000000 : ℝ)*X 1 1+(4153463117/10000000000 : ℝ)*X 1 2+(4330649091/10000000000 : ℝ)*X 2 0+(4514993711/10000000000 : ℝ)*X 2 1+(4153463117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22516783364662568921042613/3200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1530118797/100000000000000 : ℝ)*(base19) + (211119109/12500000000000 : ℝ)*(base23) + (13237171/100000000000000 : ℝ)*(lower2) + (63960771/25000000000000 : ℝ)*(upper3) + (72490493/100000000000000 : ℝ)*(lower4) + (4230889291343979/100000000000000 : ℝ)*(major0) + (4230889291343979/100000000000000 : ℝ)*(major1) + (4230889291343979/100000000000000 : ℝ)*(major2) + (571618111580203/10000000000000 : ℝ)*(sp0) + (5716202385570899/100000000000000 : ℝ)*(sp1) + (714525278342103/12500000000000 : ℝ)*(sp2) + (686389121417057/25000000000000 : ℝ)*(sp3) + (11399943833/50000000000000 : ℝ)*(sp4) + (17946780197/100000000000000 : ℝ)*(sp7) + (343196804056053/12500000000000 : ℝ)*(f.failure) + (178631372365303/3125000000000 : ℝ)*(f.sum) + (398763390953/640000000000000000000000000 : ℝ)*base66 + (23534490012118043/6400000000000000000000000000000 : ℝ)*base68 + (40793443791318043/6400000000000000000000000000000 : ℝ)*base70 + (70888074760918043/6400000000000000000000000000000 : ℝ)*base72 + (275409013527/640000000000000000000000000 : ℝ)*base73 + (58054043477718043/6400000000000000000000000000000 : ℝ)*base76 + (40724106152918043/6400000000000000000000000000000 : ℝ)*base78 + (36073719746518043/6400000000000000000000000000000 : ℝ)*base80 + (3020972006633/640000000000000000000000000 : ℝ)*base82 + (1371897/125000000000000000000 : ℝ)*base90 + (1371897/125000000000000000000 : ℝ)*base92 + (1371897/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50193027976857598680429/7040000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634148577/50000000000000 : ℝ)*(base19) + (1380694791/100000000000000 : ℝ)*(base23) + (144882871/100000000000000 : ℝ)*(upper3) + (356573/800000000000 : ℝ)*(lower4) + (15504327/10000000000000 : ℝ)*(upper5) + (4262391367576547/100000000000000 : ℝ)*(major0) + (4262391367576547/100000000000000 : ℝ)*(major1) + (4262391367576547/100000000000000 : ℝ)*(major2) + (1247341613/5000000000000 : ℝ)*(sp1) + (26245591329/100000000000000 : ℝ)*(sp2) + (5758765248156303/100000000000000 : ℝ)*(sp4) + (5758739033026889/100000000000000 : ℝ)*(sp5) + (5758737621870183/100000000000000 : ℝ)*(sp6) + (691504312335101/25000000000000 : ℝ)*(sp7) + (691504312335101/25000000000000 : ℝ)*(f.failure) + (5758765248156303/100000000000000 : ℝ)*(f.sum) + (7332394970939/7040000000000000000000000000 : ℝ)*base66 + (114116942879233489/70400000000000000000000000000000 : ℝ)*base68 + (274566279346433489/70400000000000000000000000000000 : ℝ)*base70 + (459008865267966511/70400000000000000000000000000000 : ℝ)*base71 + (55801666036539/7040000000000000000000000000 : ℝ)*base74 + (594935812856833489/70400000000000000000000000000000 : ℝ)*base76 + (90653617101566511/70400000000000000000000000000000 : ℝ)*base77 + (477279890682366511/70400000000000000000000000000000 : ℝ)*base79 + (27395178458939/7040000000000000000000000000 : ℝ)*base82 + (979951/250000000000000000000 : ℝ)*base89 + (979951/250000000000000000000 : ℝ)*base91 + (979951/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1326_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7513/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1326_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1326_s5_0 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028910169/5000000000 : ℝ)*x 0 + (84593437/156250000 : ℝ)*x 1 + (5243691263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028910169/5000000000 : ℝ)^2143 ≤ (6263885487411/50000000000000 : ℝ)^1631 := by
    have hnat : (1028910169 : ℕ)^2143*50000000000000^1631 ≤ 6263885487411^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028910169 5000000000 6263885487411 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84593437/156250000 : ℝ)^2143 ≤ (44654246423709/100000000000000 : ℝ)^1631 := by
    have hnat : (84593437 : ℕ)^2143*100000000000000^1631 ≤ 44654246423709^1631*156250000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84593437 156250000 44654246423709 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243691263/10000000000 : ℝ)^2143 ≤ (42817982586031/100000000000000 : ℝ)^1631 := by
    have hnat : (5243691263 : ℕ)^2143*100000000000000^1631 ≤ 42817982586031^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243691263 10000000000 42817982586031 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028910169/5000000000 : ℝ), (84593437/156250000 : ℝ), (5243691263/10000000000 : ℝ)] ![(6263885487411/50000000000000 : ℝ), (44654246423709/100000000000000 : ℝ), (42817982586031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028910169/5000000000 : ℝ)|^2143 ≤ (6263885487411/50000000000000 : ℝ)^1631
        have hw : |(-1028910169/5000000000 : ℝ)|=(1028910169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84593437/156250000 : ℝ)|^2143 ≤ (44654246423709/100000000000000 : ℝ)^1631
        have hw : |(84593437/156250000 : ℝ)|=(84593437/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243691263/10000000000 : ℝ)|^2143 ≤ (42817982586031/100000000000000 : ℝ)^1631
        have hw : |(5243691263/10000000000 : ℝ)|=(5243691263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_1 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (133734561/250000000 : ℝ)*x 0 + (-2144604287/10000000000 : ℝ)*x 1 + (5243691519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133734561/250000000 : ℝ)^2143 ≤ (43955509173383/100000000000000 : ℝ)^1631 := by
    have hnat : (133734561 : ℕ)^2143*100000000000000^1631 ≤ 43955509173383^1631*250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133734561 250000000 43955509173383 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144604287/10000000000 : ℝ)^2143 ≤ (13226505486391/100000000000000 : ℝ)^1631 := by
    have hnat : (2144604287 : ℕ)^2143*100000000000000^1631 ≤ 13226505486391^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144604287 10000000000 13226505486391 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243691519/10000000000 : ℝ)^2143 ≤ (21408992666321/50000000000000 : ℝ)^1631 := by
    have hnat : (5243691519 : ℕ)^2143*50000000000000^1631 ≤ 21408992666321^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243691519 10000000000 21408992666321 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133734561/250000000 : ℝ), (-2144604287/10000000000 : ℝ), (5243691519/10000000000 : ℝ)] ![(43955509173383/100000000000000 : ℝ), (13226505486391/100000000000000 : ℝ), (21408992666321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133734561/250000000 : ℝ)|^2143 ≤ (43955509173383/100000000000000 : ℝ)^1631
        have hw : |(133734561/250000000 : ℝ)|=(133734561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144604287/10000000000 : ℝ)|^2143 ≤ (13226505486391/100000000000000 : ℝ)^1631
        have hw : |(-2144604287/10000000000 : ℝ)|=(2144604287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243691519/10000000000 : ℝ)|^2143 ≤ (21408992666321/50000000000000 : ℝ)^1631
        have hw : |(5243691519/10000000000 : ℝ)|=(5243691519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_2 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668672723/1250000000 : ℝ)*x 0 + (209747673/400000000 : ℝ)*x 1 + (-536151189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668672723/1250000000 : ℝ)^2143 ≤ (43955502090963/100000000000000 : ℝ)^1631 := by
    have hnat : (668672723 : ℕ)^2143*100000000000000^1631 ≤ 43955502090963^1631*1250000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668672723 1250000000 43955502090963 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209747673/400000000 : ℝ)^2143 ≤ (21408994307851/50000000000000 : ℝ)^1631 := by
    have hnat : (209747673 : ℕ)^2143*50000000000000^1631 ≤ 21408994307851^1631*400000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209747673 400000000 21408994307851 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536151189/2500000000 : ℝ)^2143 ≤ (3306627321719/25000000000000 : ℝ)^1631 := by
    have hnat : (536151189 : ℕ)^2143*25000000000000^1631 ≤ 3306627321719^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536151189 2500000000 3306627321719 25000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668672723/1250000000 : ℝ), (209747673/400000000 : ℝ), (-536151189/2500000000 : ℝ)] ![(43955502090963/100000000000000 : ℝ), (21408994307851/50000000000000 : ℝ), (3306627321719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668672723/1250000000 : ℝ)|^2143 ≤ (43955502090963/100000000000000 : ℝ)^1631
        have hw : |(668672723/1250000000 : ℝ)|=(668672723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209747673/400000000 : ℝ)|^2143 ≤ (21408994307851/50000000000000 : ℝ)^1631
        have hw : |(209747673/400000000 : ℝ)|=(209747673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536151189/2500000000 : ℝ)|^2143 ≤ (3306627321719/25000000000000 : ℝ)^1631
        have hw : |(-536151189/2500000000 : ℝ)|=(536151189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_3 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4330788507/10000000000 : ℝ)*x 0 + (1039234111/2500000000 : ℝ)*x 1 + (4511471723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330788507/10000000000 : ℝ)^2143 ≤ (33302655506533/100000000000000 : ℝ)^1631 := by
    have hnat : (4330788507 : ℕ)^2143*100000000000000^1631 ≤ 33302655506533^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330788507 10000000000 33302655506533 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039234111/2500000000 : ℝ)^2143 ≤ (31557278907983/100000000000000 : ℝ)^1631 := by
    have hnat : (1039234111 : ℕ)^2143*100000000000000^1631 ≤ 31557278907983^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039234111 2500000000 31557278907983 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511471723/10000000000 : ℝ)^2143 ≤ (2196254097813/6250000000000 : ℝ)^1631 := by
    have hnat : (4511471723 : ℕ)^2143*6250000000000^1631 ≤ 2196254097813^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511471723 10000000000 2196254097813 6250000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330788507/10000000000 : ℝ), (1039234111/2500000000 : ℝ), (4511471723/10000000000 : ℝ)] ![(33302655506533/100000000000000 : ℝ), (31557278907983/100000000000000 : ℝ), (2196254097813/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330788507/10000000000 : ℝ)|^2143 ≤ (33302655506533/100000000000000 : ℝ)^1631
        have hw : |(4330788507/10000000000 : ℝ)|=(4330788507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039234111/2500000000 : ℝ)|^2143 ≤ (31557278907983/100000000000000 : ℝ)^1631
        have hw : |(1039234111/2500000000 : ℝ)|=(1039234111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511471723/10000000000 : ℝ)|^2143 ≤ (2196254097813/6250000000000 : ℝ)^1631
        have hw : |(4511471723/10000000000 : ℝ)|=(4511471723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_4 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057832227/10000000000 : ℝ)*x 0 + (1311075881/2500000000 : ℝ)*x 1 + (5413365021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057832227/10000000000 : ℝ)^2143 ≤ (12527866074771/100000000000000 : ℝ)^1631 := by
    have hnat : (2057832227 : ℕ)^2143*100000000000000^1631 ≤ 12527866074771^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057832227 10000000000 12527866074771 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311075881/2500000000 : ℝ)^2143 ≤ (1712982065009/4000000000000 : ℝ)^1631 := by
    have hnat : (1311075881 : ℕ)^2143*4000000000000^1631 ≤ 1712982065009^1631*2500000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311075881 2500000000 1712982065009 4000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413365021/10000000000 : ℝ)^2143 ≤ (2232379114061/5000000000000 : ℝ)^1631 := by
    have hnat : (5413365021 : ℕ)^2143*5000000000000^1631 ≤ 2232379114061^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413365021 10000000000 2232379114061 5000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057832227/10000000000 : ℝ), (1311075881/2500000000 : ℝ), (5413365021/10000000000 : ℝ)] ![(12527866074771/100000000000000 : ℝ), (1712982065009/4000000000000 : ℝ), (2232379114061/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057832227/10000000000 : ℝ)|^2143 ≤ (12527866074771/100000000000000 : ℝ)^1631
        have hw : |(-2057832227/10000000000 : ℝ)|=(2057832227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311075881/2500000000 : ℝ)|^2143 ≤ (1712982065009/4000000000000 : ℝ)^1631
        have hw : |(1311075881/2500000000 : ℝ)|=(1311075881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413365021/10000000000 : ℝ)|^2143 ≤ (2232379114061/5000000000000 : ℝ)^1631
        have hw : |(5413365021/10000000000 : ℝ)|=(5413365021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_5 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652800983/5000000000 : ℝ)*x 0 + (-987465401/5000000000 : ℝ)*x 1 + (2706682511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652800983/5000000000 : ℝ)^2143 ≤ (21741723587369/50000000000000 : ℝ)^1631 := by
    have hnat : (2652800983 : ℕ)^2143*50000000000000^1631 ≤ 21741723587369^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652800983 5000000000 21741723587369 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987465401/5000000000 : ℝ)^2143 ≤ (5934485256391/50000000000000 : ℝ)^1631 := by
    have hnat : (987465401 : ℕ)^2143*50000000000000^1631 ≤ 5934485256391^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987465401 5000000000 5934485256391 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706682511/5000000000 : ℝ)^2143 ≤ (5580947786507/12500000000000 : ℝ)^1631 := by
    have hnat : (2706682511 : ℕ)^2143*12500000000000^1631 ≤ 5580947786507^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706682511 5000000000 5580947786507 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652800983/5000000000 : ℝ), (-987465401/5000000000 : ℝ), (2706682511/5000000000 : ℝ)] ![(21741723587369/50000000000000 : ℝ), (5934485256391/50000000000000 : ℝ), (5580947786507/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652800983/5000000000 : ℝ)|^2143 ≤ (21741723587369/50000000000000 : ℝ)^1631
        have hw : |(2652800983/5000000000 : ℝ)|=(2652800983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987465401/5000000000 : ℝ)|^2143 ≤ (5934485256391/50000000000000 : ℝ)^1631
        have hw : |(-987465401/5000000000 : ℝ)|=(987465401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706682511/5000000000 : ℝ)|^2143 ≤ (5580947786507/12500000000000 : ℝ)^1631
        have hw : |(2706682511/5000000000 : ℝ)|=(2706682511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_6 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305601967/10000000000 : ℝ)*x 0 + (2706682511/5000000000 : ℝ)*x 1 + (-987465401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305601967/10000000000 : ℝ)^2143 ≤ (43483447185507/100000000000000 : ℝ)^1631 := by
    have hnat : (5305601967 : ℕ)^2143*100000000000000^1631 ≤ 43483447185507^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305601967 10000000000 43483447185507 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706682511/5000000000 : ℝ)^2143 ≤ (5580947786507/12500000000000 : ℝ)^1631 := by
    have hnat : (2706682511 : ℕ)^2143*12500000000000^1631 ≤ 5580947786507^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706682511 5000000000 5580947786507 12500000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987465401/5000000000 : ℝ)^2143 ≤ (5934485256391/50000000000000 : ℝ)^1631 := by
    have hnat : (987465401 : ℕ)^2143*50000000000000^1631 ≤ 5934485256391^1631*5000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987465401 5000000000 5934485256391 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305601967/10000000000 : ℝ), (2706682511/5000000000 : ℝ), (-987465401/5000000000 : ℝ)] ![(43483447185507/100000000000000 : ℝ), (5580947786507/12500000000000 : ℝ), (5934485256391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305601967/10000000000 : ℝ)|^2143 ≤ (43483447185507/100000000000000 : ℝ)^1631
        have hw : |(5305601967/10000000000 : ℝ)|=(5305601967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706682511/5000000000 : ℝ)|^2143 ≤ (5580947786507/12500000000000 : ℝ)^1631
        have hw : |(2706682511/5000000000 : ℝ)|=(2706682511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987465401/5000000000 : ℝ)|^2143 ≤ (5934485256391/50000000000000 : ℝ)^1631
        have hw : |(-987465401/5000000000 : ℝ)|=(987465401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1326_s5_7 (p : ℝ) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4330814989/10000000000 : ℝ)*x 0 + (451019769/1000000000 : ℝ)*x 1 + (4158216691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330814989/10000000000 : ℝ)^2143 ≤ (33302923072761/100000000000000 : ℝ)^1631 := by
    have hnat : (4330814989 : ℕ)^2143*100000000000000^1631 ≤ 33302923072761^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330814989 10000000000 33302923072761 100000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451019769/1000000000 : ℝ)^2143 ≤ (17563513737673/50000000000000 : ℝ)^1631 := by
    have hnat : (451019769 : ℕ)^2143*50000000000000^1631 ≤ 17563513737673^1631*1000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451019769 1000000000 17563513737673 50000000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158216691/10000000000 : ℝ)^2143 ≤ (1973128090261/6250000000000 : ℝ)^1631 := by
    have hnat : (4158216691 : ℕ)^2143*6250000000000^1631 ≤ 1973128090261^1631*10000000000^2143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158216691 10000000000 1973128090261 6250000000000 2143 1631 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2143/512 : ℝ)) 2143 1631 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330814989/10000000000 : ℝ), (451019769/1000000000 : ℝ), (4158216691/10000000000 : ℝ)] ![(33302923072761/100000000000000 : ℝ), (17563513737673/50000000000000 : ℝ), (1973128090261/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330814989/10000000000 : ℝ)|^2143 ≤ (33302923072761/100000000000000 : ℝ)^1631
        have hw : |(4330814989/10000000000 : ℝ)|=(4330814989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451019769/1000000000 : ℝ)|^2143 ≤ (17563513737673/50000000000000 : ℝ)^1631
        have hw : |(451019769/1000000000 : ℝ)|=(451019769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158216691/10000000000 : ℝ)|^2143 ≤ (1973128090261/6250000000000 : ℝ)^1631
        have hw : |(4158216691/10000000000 : ℝ)|=(4158216691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1326_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5551/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5527/50000 : ℝ) ^ (4285/1024 : ℝ) ≤ (9943514900275471/100000000000000000000 : ℝ) := by
    have hpowers : (5527/50000 : ℝ)^4285 ≤ (9943514900275471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5527 : ℕ)^4285*100000000000000000000^1024 ≤ 9943514900275471^1024*50000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5527 50000 9943514900275471 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5527/50000 : ℝ)) (X := (9943514900275471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (4285/1024 : ℝ) ≤ (33313021457613449/100000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^4285 ≤ (33313021457613449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14757 : ℕ)^4285*100000000000000000000^1024 ≤ 33313021457613449^1024*100000^4285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 33313021457613449 100000000000000000000 4285 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (33313021457613449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009943514900275471/50000000000000000000 : ℝ) ≤ (5000237605340377/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (50009943514900275471/50000000000000000000 : ℝ)^1024 ≤ (5000237605340377/5000000000000000 : ℝ)^4285 := by
      have hnat : (50009943514900275471 : ℕ)^1024*5000000000000000^4285 ≤ 5000237605340377^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009943514900275471 50000000000000000000 5000237605340377 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000237605340377/5000000000000000 : ℝ)) (X := (50009943514900275471/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501081413408947223/2500000000000000000 : ℝ) ≤ (5000516772512379/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (2501081413408947223/2500000000000000000 : ℝ)^1024 ≤ (5000516772512379/5000000000000000 : ℝ)^4285 := by
      have hnat : (2501081413408947223 : ℕ)^1024*5000000000000000^4285 ≤ 5000516772512379^4285*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501081413408947223 2500000000000000000 5000516772512379 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000516772512379/5000000000000000 : ℝ)) (X := (2501081413408947223/2500000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033313021457613449/50000000000000000000 : ℝ) ≤ (5000795939684381/5000000000000000 : ℝ) ^ (4285/1024 : ℝ) := by
    have hpowers : (50033313021457613449/50000000000000000000 : ℝ)^1024 ≤ (5000795939684381/5000000000000000 : ℝ)^4285 := by
      have hnat : (50033313021457613449 : ℕ)^1024*5000000000000000^4285 ≤ 5000795939684381^4285*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033313021457613449 50000000000000000000 5000795939684381 5000000000000000 1024 4285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000795939684381/5000000000000000 : ℝ)) (X := (50033313021457613449/50000000000000000000 : ℝ)) (by norm_num) 4285 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9943514900275471/100000000000000000000 : ℝ) ≤ ((3701941604947359163/3703000000000000000 : ℝ)+2*(139583586001/92575000000000 : ℝ)*(5527/50000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (3701941604947359163/3703000000000000000 : ℝ)+2*(139583586001/92575000000000 : ℝ)*(5527/50000 : ℝ)=(5000237605340377/5000000000000000 : ℝ) by norm_num, show 1+2*(9943514900275471/100000000000000000000 : ℝ)=(50009943514900275471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33313021457613449/100000000000000000000 : ℝ)+(9943514900275471/100000000000000000000 : ℝ) ≤ ((3701941604947359163/3703000000000000000 : ℝ)+(139583586001/92575000000000 : ℝ)*((14757/100000 : ℝ)+(5527/50000 : ℝ)))^(4285/1024 : ℝ) := by
    rw [show (3701941604947359163/3703000000000000000 : ℝ)+(139583586001/92575000000000 : ℝ)*((14757/100000 : ℝ)+(5527/50000 : ℝ))=(5000516772512379/5000000000000000 : ℝ) by norm_num, show 1+(33313021457613449/100000000000000000000 : ℝ)+(9943514900275471/100000000000000000000 : ℝ)=(2501081413408947223/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33313021457613449/100000000000000000000 : ℝ) ≤ ((3701941604947359163/3703000000000000000 : ℝ)+2*(139583586001/92575000000000 : ℝ)*(14757/100000 : ℝ))^(4285/1024 : ℝ) := by
    rw [show (3701941604947359163/3703000000000000000 : ℝ)+2*(139583586001/92575000000000 : ℝ)*(14757/100000 : ℝ)=(5000795939684381/5000000000000000 : ℝ) by norm_num, show 1+2*(33313021457613449/100000000000000000000 : ℝ)=(50033313021457613449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3701941604947359163/3703000000000000000 : ℝ)*(X 1 0+X 2 0)+(139583586001/92575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (3701941604947359163/3703000000000000000 : ℝ)) (alpha := (139583586001/92575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3701941604947359163/3703000000000000000 : ℝ)*(X 0 1+X 2 1)+(139583586001/92575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (3701941604947359163/3703000000000000000 : ℝ)) (alpha := (139583586001/92575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3701941604947359163/3703000000000000000 : ℝ)*(X 0 2+X 1 2)+(139583586001/92575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4285/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (3701941604947359163/3703000000000000000 : ℝ)) (alpha := (139583586001/92575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1028910169/5000000000 : ℝ)*X 0 0+(84593437/156250000 : ℝ)*X 0 1+(5243691263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133734561/250000000 : ℝ)*X 1 0+(-2144604287/10000000000 : ℝ)*X 1 1+(5243691519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668672723/1250000000 : ℝ)*X 2 0+(209747673/400000000 : ℝ)*X 2 1+(-536151189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330788507/10000000000 : ℝ)*X 0 0+(1039234111/2500000000 : ℝ)*X 0 1+(4511471723/10000000000 : ℝ)*X 0 2+(4330788507/10000000000 : ℝ)*X 1 0+(1039234111/2500000000 : ℝ)*X 1 1+(4511471723/10000000000 : ℝ)*X 1 2+(4330788507/10000000000 : ℝ)*X 2 0+(1039234111/2500000000 : ℝ)*X 2 1+(4511471723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2057832227/10000000000 : ℝ)*X 0 0+(1311075881/2500000000 : ℝ)*X 0 1+(5413365021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652800983/5000000000 : ℝ)*X 1 0+(-987465401/5000000000 : ℝ)*X 1 1+(2706682511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305601967/10000000000 : ℝ)*X 2 0+(2706682511/5000000000 : ℝ)*X 2 1+(-987465401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330814989/10000000000 : ℝ)*X 0 0+(451019769/1000000000 : ℝ)*X 0 1+(4158216691/10000000000 : ℝ)*X 0 2+(4330814989/10000000000 : ℝ)*X 1 0+(451019769/1000000000 : ℝ)*X 1 1+(4158216691/10000000000 : ℝ)*X 1 2+(4330814989/10000000000 : ℝ)*X 2 0+(451019769/1000000000 : ℝ)*X 2 1+(4158216691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1326_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (781524212117758154485551/165312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (508031151/50000000000000 : ℝ)*(base19) + (148080231/25000000000000 : ℝ)*(base23) + (306723499/100000000000000 : ℝ)*(upper2) + (482783091/100000000000000 : ℝ)*(upper3) + (578781/390625000000 : ℝ)*(upper4) + (27165733038829/625000000000 : ℝ)*(major0) + (27165733038829/625000000000 : ℝ)*(major1) + (27165733038829/625000000000 : ℝ)*(major2) + (5872415978037341/100000000000000 : ℝ)*(sp0) + (1468105962722517/25000000000000 : ℝ)*(sp1) + (1174484854926289/20000000000000 : ℝ)*(sp2) + (1410299991381157/50000000000000 : ℝ)*(sp3) + (8888915029/100000000000000 : ℝ)*(sp4) + (4782562679/50000000000000 : ℝ)*(sp7) + (352576193485959/12500000000000 : ℝ)*(f.failure) + (587242486695237/10000000000000 : ℝ)*(f.sum) + (683081109873/105800000000000000000000000 : ℝ)*base65 + (5236957231482161/330625000000000000000000000000 : ℝ)*base67 + (2231110470739661/330625000000000000000000000000 : ℝ)*base69 + (1815887629394661/330625000000000000000000000000 : ℝ)*base71 + (283458413917/66125000000000000000000000 : ℝ)*base73 + (7966237190114661/330625000000000000000000000000 : ℝ)*base75 + (6091863412619661/330625000000000000000000000000 : ℝ)*base77 + (165895002821923/10332031250000000000000000000 : ℝ)*base79 + (44074477101/132250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1217891/125000000000000000000 : ℝ)*base90 + (1217891/125000000000000000000 : ℝ)*base92 + (1217891/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297338780755198104990406053/92575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17597229/3125000000000 : ℝ)*(base19) + (307037377/50000000000000 : ℝ)*(base23) + (32920261/50000000000000 : ℝ)*(upper3) + (900511/4000000000000 : ℝ)*(lower4) + (33181419/50000000000000 : ℝ)*(upper5) + (2189017328169677/50000000000000 : ℝ)*(major0) + (2189017328169677/50000000000000 : ℝ)*(major1) + (2189017328169677/50000000000000 : ℝ)*(major2) + (364049/3200000000 : ℝ)*(sp1) + (6137746349/50000000000000 : ℝ)*(sp2) + (5915006916085271/100000000000000 : ℝ)*(sp4) + (2957497488221347/50000000000000 : ℝ)*(sp5) + (5914994026517819/100000000000000 : ℝ)*(sp6) + (355132786191391/12500000000000 : ℝ)*(sp7) + (355132786191391/12500000000000 : ℝ)*(f.failure) + (5915006916085271/100000000000000 : ℝ)*(f.sum) + (100870118490209/18515000000000000000000000000 : ℝ)*base66 + (1250351236853180351/185150000000000000000000000000000 : ℝ)*base67 + (1597935969994069649/185150000000000000000000000000000 : ℝ)*base70 + (489202383667619649/185150000000000000000000000000000 : ℝ)*base72 + (19920867745843/9257500000000000000000000000 : ℝ)*base73 + (980611122338119649/185150000000000000000000000000000 : ℝ)*base76 + (1155082031627230351/185150000000000000000000000000000 : ℝ)*base77 + (822278196866419649/185150000000000000000000000000000 : ℝ)*base80 + (64450690648707/9257500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (292741/125000000000000000000 : ℝ)*base89 + (292741/125000000000000000000 : ℝ)*base91 + (292741/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1326_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1326_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1326_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1326_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1326_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1326_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4285/1024 : ℝ) ≤ p) (hpb : p ≤ (2143/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15409851/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1949/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1326_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
