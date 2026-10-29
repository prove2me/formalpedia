-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1458_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:44.81798+00:00
-- url     : https://prove2.me/submissions/9bf797bd-2f21-4256-bb9a-c72529f94d2e

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
theorem support_rectangle_w1458_s6_0 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947842709/10000000000 : ℝ)*x 0 + (5406724981/10000000000 : ℝ)*x 1 + (655939567/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947842709/10000000000 : ℝ)^2209 ≤ (11890660224107/100000000000000 : ℝ)^1697 := by
    have hnat : (1947842709 : ℕ)^2209*100000000000000^1697 ≤ 11890660224107^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947842709 10000000000 11890660224107 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406724981/10000000000 : ℝ)^2209 ≤ (22455781781211/50000000000000 : ℝ)^1697 := by
    have hnat : (5406724981 : ℕ)^2209*50000000000000^1697 ≤ 22455781781211^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406724981 10000000000 22455781781211 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655939567/1250000000 : ℝ)^2209 ≤ (43197776204317/100000000000000 : ℝ)^1697 := by
    have hnat : (655939567 : ℕ)^2209*100000000000000^1697 ≤ 43197776204317^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655939567 1250000000 43197776204317 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947842709/10000000000 : ℝ), (5406724981/10000000000 : ℝ), (655939567/1250000000 : ℝ)] ![(11890660224107/100000000000000 : ℝ), (22455781781211/50000000000000 : ℝ), (43197776204317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947842709/10000000000 : ℝ)|^2209 ≤ (11890660224107/100000000000000 : ℝ)^1697
        have hw : |(-1947842709/10000000000 : ℝ)|=(1947842709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406724981/10000000000 : ℝ)|^2209 ≤ (22455781781211/50000000000000 : ℝ)^1697
        have hw : |(5406724981/10000000000 : ℝ)|=(5406724981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655939567/1250000000 : ℝ)|^2209 ≤ (43197776204317/100000000000000 : ℝ)^1697
        have hw : |(655939567/1250000000 : ℝ)|=(655939567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_1 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346700867/10000000000 : ℝ)*x 0 + (-1014438979/5000000000 : ℝ)*x 1 + (2623758439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346700867/10000000000 : ℝ)^2209 ≤ (553295315033/1250000000000 : ℝ)^1697 := by
    have hnat : (5346700867 : ℕ)^2209*1250000000000^1697 ≤ 553295315033^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346700867 10000000000 553295315033 1250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014438979/5000000000 : ℝ)^2209 ≤ (1567324365389/12500000000000 : ℝ)^1697 := by
    have hnat : (1014438979 : ℕ)^2209*12500000000000^1697 ≤ 1567324365389^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014438979 5000000000 1567324365389 12500000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623758439/5000000000 : ℝ)^2209 ≤ (21598889934547/50000000000000 : ℝ)^1697 := by
    have hnat : (2623758439 : ℕ)^2209*50000000000000^1697 ≤ 21598889934547^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623758439 5000000000 21598889934547 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346700867/10000000000 : ℝ), (-1014438979/5000000000 : ℝ), (2623758439/5000000000 : ℝ)] ![(553295315033/1250000000000 : ℝ), (1567324365389/12500000000000 : ℝ), (21598889934547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346700867/10000000000 : ℝ)|^2209 ≤ (553295315033/1250000000000 : ℝ)^1697
        have hw : |(5346700867/10000000000 : ℝ)|=(5346700867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1014438979/5000000000 : ℝ)|^2209 ≤ (1567324365389/12500000000000 : ℝ)^1697
        have hw : |(-1014438979/5000000000 : ℝ)|=(1014438979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623758439/5000000000 : ℝ)|^2209 ≤ (21598889934547/50000000000000 : ℝ)^1697
        have hw : |(2623758439/5000000000 : ℝ)|=(2623758439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_2 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346700269/10000000000 : ℝ)*x 0 + (2623758667/5000000000 : ℝ)*x 1 + (-2028878151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346700269/10000000000 : ℝ)^2209 ≤ (8852723751667/20000000000000 : ℝ)^1697 := by
    have hnat : (5346700269 : ℕ)^2209*20000000000000^1697 ≤ 8852723751667^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346700269 10000000000 8852723751667 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623758667/5000000000 : ℝ)^2209 ≤ (5399723094433/12500000000000 : ℝ)^1697 := by
    have hnat : (2623758667 : ℕ)^2209*12500000000000^1697 ≤ 5399723094433^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623758667 5000000000 5399723094433 12500000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028878151/10000000000 : ℝ)^2209 ≤ (783662279733/6250000000000 : ℝ)^1697 := by
    have hnat : (2028878151 : ℕ)^2209*6250000000000^1697 ≤ 783662279733^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028878151 10000000000 783662279733 6250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346700269/10000000000 : ℝ), (2623758667/5000000000 : ℝ), (-2028878151/10000000000 : ℝ)] ![(8852723751667/20000000000000 : ℝ), (5399723094433/12500000000000 : ℝ), (783662279733/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346700269/10000000000 : ℝ)|^2209 ≤ (8852723751667/20000000000000 : ℝ)^1697
        have hw : |(5346700269/10000000000 : ℝ)|=(5346700269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623758667/5000000000 : ℝ)|^2209 ≤ (5399723094433/12500000000000 : ℝ)^1697
        have hw : |(2623758667/5000000000 : ℝ)|=(2623758667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028878151/10000000000 : ℝ)|^2209 ≤ (783662279733/6250000000000 : ℝ)^1697
        have hw : |(-2028878151/10000000000 : ℝ)|=(2028878151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_3 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297174787/10000000000 : ℝ)*x 0 + (412626419/1000000000 : ℝ)*x 1 + (2237173299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297174787/10000000000 : ℝ)^2209 ≤ (104078516531/312500000000 : ℝ)^1697 := by
    have hnat : (4297174787 : ℕ)^2209*312500000000^1697 ≤ 104078516531^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297174787 10000000000 104078516531 312500000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412626419/1000000000 : ℝ)^2209 ≤ (7897818972127/25000000000000 : ℝ)^1697 := by
    have hnat : (412626419 : ℕ)^2209*25000000000000^1697 ≤ 7897818972127^1697*1000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412626419 1000000000 7897818972127 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237173299/5000000000 : ℝ)^2209 ≤ (35103598803881/100000000000000 : ℝ)^1697 := by
    have hnat : (2237173299 : ℕ)^2209*100000000000000^1697 ≤ 35103598803881^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237173299 5000000000 35103598803881 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297174787/10000000000 : ℝ), (412626419/1000000000 : ℝ), (2237173299/5000000000 : ℝ)] ![(104078516531/312500000000 : ℝ), (7897818972127/25000000000000 : ℝ), (35103598803881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297174787/10000000000 : ℝ)|^2209 ≤ (104078516531/312500000000 : ℝ)^1697
        have hw : |(4297174787/10000000000 : ℝ)|=(4297174787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412626419/1000000000 : ℝ)|^2209 ≤ (7897818972127/25000000000000 : ℝ)^1697
        have hw : |(412626419/1000000000 : ℝ)|=(412626419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237173299/5000000000 : ℝ)|^2209 ≤ (35103598803881/100000000000000 : ℝ)^1697
        have hw : |(2237173299/5000000000 : ℝ)|=(2237173299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_4 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-389570661/2000000000 : ℝ)*x 0 + (5248092801/10000000000 : ℝ)*x 1 + (1351536521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389570661/2000000000 : ℝ)^2209 ≤ (2378148884673/20000000000000 : ℝ)^1697 := by
    have hnat : (389570661 : ℕ)^2209*20000000000000^1697 ≤ 2378148884673^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389570661 2000000000 2378148884673 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5248092801/10000000000 : ℝ)^2209 ≤ (43203951402291/100000000000000 : ℝ)^1697 := by
    have hnat : (5248092801 : ℕ)^2209*100000000000000^1697 ≤ 43203951402291^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248092801 10000000000 43203951402291 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351536521/2500000000 : ℝ)^2209 ≤ (2806581510739/6250000000000 : ℝ)^1697 := by
    have hnat : (1351536521 : ℕ)^2209*6250000000000^1697 ≤ 2806581510739^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351536521 2500000000 2806581510739 6250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389570661/2000000000 : ℝ), (5248092801/10000000000 : ℝ), (1351536521/2500000000 : ℝ)] ![(2378148884673/20000000000000 : ℝ), (43203951402291/100000000000000 : ℝ), (2806581510739/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389570661/2000000000 : ℝ)|^2209 ≤ (2378148884673/20000000000000 : ℝ)^1697
        have hw : |(-389570661/2000000000 : ℝ)|=(389570661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5248092801/10000000000 : ℝ)|^2209 ≤ (43203951402291/100000000000000 : ℝ)^1697
        have hw : |(5248092801/10000000000 : ℝ)|=(5248092801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351536521/2500000000 : ℝ)|^2209 ≤ (2806581510739/6250000000000 : ℝ)^1697
        have hw : |(1351536521/2500000000 : ℝ)|=(1351536521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_5 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326299151/2500000000 : ℝ)*x 0 + (-935124483/5000000000 : ℝ)*x 1 + (1081229177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326299151/2500000000 : ℝ)^2209 ≤ (10954220517989/25000000000000 : ℝ)^1697 := by
    have hnat : (1326299151 : ℕ)^2209*25000000000000^1697 ≤ 10954220517989^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326299151 2500000000 10954220517989 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935124483/5000000000 : ℝ)^2209 ≤ (5638907947271/50000000000000 : ℝ)^1697 := by
    have hnat : (935124483 : ℕ)^2209*50000000000000^1697 ≤ 5638907947271^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935124483 5000000000 5638907947271 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081229177/2000000000 : ℝ)^2209 ≤ (11226325505037/25000000000000 : ℝ)^1697 := by
    have hnat : (1081229177 : ℕ)^2209*25000000000000^1697 ≤ 11226325505037^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081229177 2000000000 11226325505037 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326299151/2500000000 : ℝ), (-935124483/5000000000 : ℝ), (1081229177/2000000000 : ℝ)] ![(10954220517989/25000000000000 : ℝ), (5638907947271/50000000000000 : ℝ), (11226325505037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326299151/2500000000 : ℝ)|^2209 ≤ (10954220517989/25000000000000 : ℝ)^1697
        have hw : |(1326299151/2500000000 : ℝ)|=(1326299151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935124483/5000000000 : ℝ)|^2209 ≤ (5638907947271/50000000000000 : ℝ)^1697
        have hw : |(-935124483/5000000000 : ℝ)|=(935124483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081229177/2000000000 : ℝ)|^2209 ≤ (11226325505037/25000000000000 : ℝ)^1697
        have hw : |(1081229177/2000000000 : ℝ)|=(1081229177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_6 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652598113/5000000000 : ℝ)*x 0 + (1351536509/2500000000 : ℝ)*x 1 + (-467562319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652598113/5000000000 : ℝ)^2209 ≤ (43816878008031/100000000000000 : ℝ)^1697 := by
    have hnat : (2652598113 : ℕ)^2209*100000000000000^1697 ≤ 43816878008031^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652598113 5000000000 43816878008031 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351536509/2500000000 : ℝ)^2209 ≤ (22452651826413/50000000000000 : ℝ)^1697 := by
    have hnat : (1351536509 : ℕ)^2209*50000000000000^1697 ≤ 22452651826413^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351536509 2500000000 22452651826413 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467562319/2500000000 : ℝ)^2209 ≤ (176215911373/1562500000000 : ℝ)^1697 := by
    have hnat : (467562319 : ℕ)^2209*1562500000000^1697 ≤ 176215911373^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467562319 2500000000 176215911373 1562500000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652598113/5000000000 : ℝ), (1351536509/2500000000 : ℝ), (-467562319/2500000000 : ℝ)] ![(43816878008031/100000000000000 : ℝ), (22452651826413/50000000000000 : ℝ), (176215911373/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652598113/5000000000 : ℝ)|^2209 ≤ (43816878008031/100000000000000 : ℝ)^1697
        have hw : |(2652598113/5000000000 : ℝ)|=(2652598113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351536509/2500000000 : ℝ)|^2209 ≤ (22452651826413/50000000000000 : ℝ)^1697
        have hw : |(1351536509/2500000000 : ℝ)|=(1351536509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467562319/2500000000 : ℝ)|^2209 ≤ (176215911373/1562500000000 : ℝ)^1697
        have hw : |(-467562319/2500000000 : ℝ)|=(467562319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s6_7 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297198661/10000000000 : ℝ)*x 0 + (1118272071/2500000000 : ℝ)*x 1 + (1031882337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297198661/10000000000 : ℝ)^2209 ≤ (2081585384467/6250000000000 : ℝ)^1697 := by
    have hnat : (4297198661 : ℕ)^2209*6250000000000^1697 ≤ 2081585384467^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297198661 10000000000 2081585384467 6250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118272071/2500000000 : ℝ)^2209 ≤ (35090748704241/100000000000000 : ℝ)^1697 := by
    have hnat : (1118272071 : ℕ)^2209*100000000000000^1697 ≤ 35090748704241^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118272071 2500000000 35090748704241 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031882337/2500000000 : ℝ)^2209 ≤ (632077702541/2000000000000 : ℝ)^1697 := by
    have hnat : (1031882337 : ℕ)^2209*2000000000000^1697 ≤ 632077702541^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031882337 2500000000 632077702541 2000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297198661/10000000000 : ℝ), (1118272071/2500000000 : ℝ), (1031882337/2500000000 : ℝ)] ![(2081585384467/6250000000000 : ℝ), (35090748704241/100000000000000 : ℝ), (632077702541/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297198661/10000000000 : ℝ)|^2209 ≤ (2081585384467/6250000000000 : ℝ)^1697
        have hw : |(4297198661/10000000000 : ℝ)|=(4297198661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118272071/2500000000 : ℝ)|^2209 ≤ (35090748704241/100000000000000 : ℝ)^1697
        have hw : |(1118272071/2500000000 : ℝ)|=(1118272071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031882337/2500000000 : ℝ)|^2209 ≤ (632077702541/2000000000000 : ℝ)^1697
        have hw : |(1031882337/2500000000 : ℝ)|=(1031882337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1458_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5699/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2279/20000 : ℝ) ^ (4417/1024 : ℝ) ≤ (4267066124658883/50000000000000000000 : ℝ) := by
    have hpowers : (2279/20000 : ℝ)^4417 ≤ (4267066124658883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2279 : ℕ)^4417*50000000000000000000^1024 ≤ 4267066124658883^1024*20000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2279 20000 4267066124658883 50000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2279/20000 : ℝ)) (X := (4267066124658883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7387/50000 : ℝ) ^ (4417/1024 : ℝ) ≤ (26160708179347627/100000000000000000000 : ℝ) := by
    have hpowers : (7387/50000 : ℝ)^4417 ≤ (26160708179347627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7387 : ℕ)^4417*100000000000000000000^1024 ≤ 26160708179347627^1024*50000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7387 50000 26160708179347627 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7387/50000 : ℝ)) (X := (26160708179347627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004267066124658883/25000000000000000000 : ℝ) ≤ (2000079134060093/2000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (25004267066124658883/25000000000000000000 : ℝ)^1024 ≤ (2000079134060093/2000000000000000 : ℝ)^4417 := by
      have hnat : (25004267066124658883 : ℕ)^1024*2000000000000000^4417 ≤ 2000079134060093^4417*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004267066124658883 25000000000000000000 2000079134060093 2000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000079134060093/2000000000000000 : ℝ)) (X := (25004267066124658883/25000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034694840428665393/100000000000000000000 : ℝ) ≤ (10000804228735841/10000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (100034694840428665393/100000000000000000000 : ℝ)^1024 ≤ (10000804228735841/10000000000000000 : ℝ)^4417 := by
      have hnat : (100034694840428665393 : ℕ)^1024*10000000000000000^4417 ≤ 10000804228735841^4417*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034694840428665393 100000000000000000000 10000804228735841 10000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000804228735841/10000000000000000 : ℝ)) (X := (100034694840428665393/100000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026160708179347627/50000000000000000000 : ℝ) ≤ (10001212787171217/10000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50026160708179347627/50000000000000000000 : ℝ)^1024 ≤ (10001212787171217/10000000000000000 : ℝ)^4417 := by
      have hnat : (50026160708179347627 : ℕ)^1024*10000000000000000^4417 ≤ 10001212787171217^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026160708179347627 50000000000000000000 10001212787171217 10000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001212787171217/10000000000000000 : ℝ)) (X := (50026160708179347627/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4267066124658883/50000000000000000000 : ℝ) ≤ ((6756405184640610439/6758000000000000000 : ℝ)+2*(25534902211/21118750000000 : ℝ)*(2279/20000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (6756405184640610439/6758000000000000000 : ℝ)+2*(25534902211/21118750000000 : ℝ)*(2279/20000 : ℝ)=(2000079134060093/2000000000000000 : ℝ) by norm_num, show 1+2*(4267066124658883/50000000000000000000 : ℝ)=(25004267066124658883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26160708179347627/100000000000000000000 : ℝ)+(4267066124658883/50000000000000000000 : ℝ) ≤ ((6756405184640610439/6758000000000000000 : ℝ)+(25534902211/21118750000000 : ℝ)*((7387/50000 : ℝ)+(2279/20000 : ℝ)))^(4417/1024 : ℝ) := by
    rw [show (6756405184640610439/6758000000000000000 : ℝ)+(25534902211/21118750000000 : ℝ)*((7387/50000 : ℝ)+(2279/20000 : ℝ))=(10000804228735841/10000000000000000 : ℝ) by norm_num, show 1+(26160708179347627/100000000000000000000 : ℝ)+(4267066124658883/50000000000000000000 : ℝ)=(100034694840428665393/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26160708179347627/100000000000000000000 : ℝ) ≤ ((6756405184640610439/6758000000000000000 : ℝ)+2*(25534902211/21118750000000 : ℝ)*(7387/50000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (6756405184640610439/6758000000000000000 : ℝ)+2*(25534902211/21118750000000 : ℝ)*(7387/50000 : ℝ)=(10001212787171217/10000000000000000 : ℝ) by norm_num, show 1+2*(26160708179347627/100000000000000000000 : ℝ)=(50026160708179347627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6756405184640610439/6758000000000000000 : ℝ)*(X 1 0+X 2 0)+(25534902211/21118750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (6756405184640610439/6758000000000000000 : ℝ)) (alpha := (25534902211/21118750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6756405184640610439/6758000000000000000 : ℝ)*(X 0 1+X 2 1)+(25534902211/21118750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (6756405184640610439/6758000000000000000 : ℝ)) (alpha := (25534902211/21118750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6756405184640610439/6758000000000000000 : ℝ)*(X 0 2+X 1 2)+(25534902211/21118750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (6756405184640610439/6758000000000000000 : ℝ)) (alpha := (25534902211/21118750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1947842709/10000000000 : ℝ)*X 0 0+(5406724981/10000000000 : ℝ)*X 0 1+(655939567/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346700867/10000000000 : ℝ)*X 1 0+(-1014438979/5000000000 : ℝ)*X 1 1+(2623758439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346700269/10000000000 : ℝ)*X 2 0+(2623758667/5000000000 : ℝ)*X 2 1+(-2028878151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297174787/10000000000 : ℝ)*X 0 0+(412626419/1000000000 : ℝ)*X 0 1+(2237173299/5000000000 : ℝ)*X 0 2+(4297174787/10000000000 : ℝ)*X 1 0+(412626419/1000000000 : ℝ)*X 1 1+(2237173299/5000000000 : ℝ)*X 1 2+(4297174787/10000000000 : ℝ)*X 2 0+(412626419/1000000000 : ℝ)*X 2 1+(2237173299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-389570661/2000000000 : ℝ)*X 0 0+(5248092801/10000000000 : ℝ)*X 0 1+(1351536521/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326299151/2500000000 : ℝ)*X 1 0+(-935124483/5000000000 : ℝ)*X 1 1+(1081229177/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652598113/5000000000 : ℝ)*X 2 0+(1351536509/2500000000 : ℝ)*X 2 1+(-467562319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4297198661/10000000000 : ℝ)*X 0 0+(1118272071/2500000000 : ℝ)*X 0 1+(1031882337/2500000000 : ℝ)*X 0 2+(4297198661/10000000000 : ℝ)*X 1 0+(1118272071/2500000000 : ℝ)*X 1 1+(1031882337/2500000000 : ℝ)*X 1 2+(4297198661/10000000000 : ℝ)*X 2 0+(1118272071/2500000000 : ℝ)*X 2 1+(1031882337/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (473987934145566741259028727/84475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173579/7812500000 : ℝ)*(base19) + (250925297/20000000000000 : ℝ)*(base23) + (6193077/20000000000000 : ℝ)*(upper2) + (551217957/100000000000000 : ℝ)*(upper3) + (86237577/50000000000000 : ℝ)*(upper4) + (1144263755308731/25000000000000 : ℝ)*(major0) + (1144263755308731/25000000000000 : ℝ)*(major1) + (1144263755308731/25000000000000 : ℝ)*(major2) + (6281142616777879/100000000000000 : ℝ)*(sp0) + (3140592876445223/50000000000000 : ℝ)*(sp1) + (6281186720075161/100000000000000 : ℝ)*(sp2) + (2872898952671493/100000000000000 : ℝ)*(sp3) + (45357923767/100000000000000 : ℝ)*(sp4) + (22928063877/100000000000000 : ℝ)*(sp7) + (287292188073537/10000000000000 : ℝ)*(f.failure) + (3140593987350823/50000000000000 : ℝ)*(f.sum) + (59255763690333/8447500000000000000000000000 : ℝ)*base66 + (1145540776702237091/168950000000000000000000000000000 : ℝ)*base68 + (1421902968674662909/168950000000000000000000000000000 : ℝ)*base69 + (301818493807937091/168950000000000000000000000000000 : ℝ)*base72 + (14023072472887/8447500000000000000000000000 : ℝ)*base73 + (1381209331071462909/168950000000000000000000000000000 : ℝ)*base75 + (1253801333689587091/168950000000000000000000000000000 : ℝ)*base78 + (2009440263748837091/168950000000000000000000000000000 : ℝ)*base80 + (80628077886819/16895000000000000000000000000 : ℝ)*base81 + (279771/62500000000000000000 : ℝ)*base90 + (279771/62500000000000000000 : ℝ)*base92 + (279771/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579587180321092790524441971/168950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7033517/781250000000 : ℝ)*(base19) + (190773537/50000000000000 : ℝ)*(base23) + (34359533/100000000000000 : ℝ)*(lower1) + (2921417/20000000000000 : ℝ)*(upper2) + (7465763/12500000000000 : ℝ)*(upper3) + (4610416777342937/100000000000000 : ℝ)*(major0) + (4610416777342937/100000000000000 : ℝ)*(major1) + (4610416777342937/100000000000000 : ℝ)*(major2) + (6101904539/50000000000000 : ℝ)*(sp1) + (133272233/12500000000000 : ℝ)*(sp3) + (3163485540895363/50000000000000 : ℝ)*(sp4) + (395434873605717/6250000000000 : ℝ)*(sp5) + (1581742675060913/25000000000000 : ℝ)*(sp6) + (1446930646183223/50000000000000 : ℝ)*(sp7) + (289386235854431/10000000000000 : ℝ)*(f.failure) + (3163485540895363/50000000000000 : ℝ)*(f.sum) + (9371838387179/2111875000000000000000000000 : ℝ)*base65 + (2741782368781359343/675800000000000000000000000000000 : ℝ)*base67 + (412023695020159343/675800000000000000000000000000000 : ℝ)*base69 + (1855265808120959343/675800000000000000000000000000000 : ℝ)*base71 + (1391270819713/4223750000000000000000000000 : ℝ)*base73 + (1240152921144159343/675800000000000000000000000000000 : ℝ)*base75 + (24283969201960559343/675800000000000000000000000000000 : ℝ)*base77 + (5492705434725440657/675800000000000000000000000000000 : ℝ)*base80 + (1438002174469/2111875000000000000000000000 : ℝ)*base81 + (303373/62500000000000000000 : ℝ)*base90 + (303373/62500000000000000000 : ℝ)*base92 + (303373/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1458_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1458_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1458_box_0 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789245413/10000000000 : ℝ)*x 0 + (13462527/25000000 : ℝ)*x 1 + (673126241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789245413/10000000000 : ℝ)^2209 ≤ (10646179279451/100000000000000 : ℝ)^1697 := by
    have hnat : (1789245413 : ℕ)^2209*100000000000000^1697 ≤ 10646179279451^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789245413 10000000000 10646179279451 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13462527/25000000 : ℝ)^2209 ≤ (44676915064789/100000000000000 : ℝ)^1697 := by
    have hnat : (13462527 : ℕ)^2209*100000000000000^1697 ≤ 44676915064789^1697*25000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13462527 25000000 44676915064789 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673126241/1250000000 : ℝ)^2209 ≤ (44676905647477/100000000000000 : ℝ)^1697 := by
    have hnat : (673126241 : ℕ)^2209*100000000000000^1697 ≤ 44676905647477^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673126241 1250000000 44676905647477 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789245413/10000000000 : ℝ), (13462527/25000000 : ℝ), (673126241/1250000000 : ℝ)] ![(10646179279451/100000000000000 : ℝ), (44676915064789/100000000000000 : ℝ), (44676905647477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789245413/10000000000 : ℝ)|^2209 ≤ (10646179279451/100000000000000 : ℝ)^1697
        have hw : |(-1789245413/10000000000 : ℝ)|=(1789245413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13462527/25000000 : ℝ)|^2209 ≤ (44676915064789/100000000000000 : ℝ)^1697
        have hw : |(13462527/25000000 : ℝ)|=(13462527/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673126241/1250000000 : ℝ)|^2209 ≤ (44676905647477/100000000000000 : ℝ)^1697
        have hw : |(673126241/1250000000 : ℝ)|=(673126241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_1 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286241751/10000000000 : ℝ)*x 0 + (-385010683/2000000000 : ℝ)*x 1 + (1346252449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286241751/10000000000 : ℝ)^2209 ≤ (218066030153/500000000000 : ℝ)^1697 := by
    have hnat : (5286241751 : ℕ)^2209*500000000000^1697 ≤ 218066030153^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286241751 10000000000 218066030153 500000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385010683/2000000000 : ℝ)^2209 ≤ (1170988973281/10000000000000 : ℝ)^1697 := by
    have hnat : (385010683 : ℕ)^2209*10000000000000^1697 ≤ 1170988973281^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385010683 2000000000 1170988973281 10000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346252449/2500000000 : ℝ)^2209 ≤ (44676904221921/100000000000000 : ℝ)^1697 := by
    have hnat : (1346252449 : ℕ)^2209*100000000000000^1697 ≤ 44676904221921^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346252449 2500000000 44676904221921 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286241751/10000000000 : ℝ), (-385010683/2000000000 : ℝ), (1346252449/2500000000 : ℝ)] ![(218066030153/500000000000 : ℝ), (1170988973281/10000000000000 : ℝ), (44676904221921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286241751/10000000000 : ℝ)|^2209 ≤ (218066030153/500000000000 : ℝ)^1697
        have hw : |(5286241751/10000000000 : ℝ)|=(5286241751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385010683/2000000000 : ℝ)|^2209 ≤ (1170988973281/10000000000000 : ℝ)^1697
        have hw : |(-385010683/2000000000 : ℝ)|=(385010683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346252449/2500000000 : ℝ)|^2209 ≤ (44676904221921/100000000000000 : ℝ)^1697
        have hw : |(1346252449/2500000000 : ℝ)|=(1346252449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_2 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321560441/2500000000 : ℝ)*x 0 + (8616017/16000000 : ℝ)*x 1 + (-962526133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321560441/2500000000 : ℝ)^2209 ≤ (21806603085107/50000000000000 : ℝ)^1697 := by
    have hnat : (1321560441 : ℕ)^2209*50000000000000^1697 ≤ 21806603085107^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321560441 2500000000 21806603085107 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8616017/16000000 : ℝ)^2209 ≤ (44676913174847/100000000000000 : ℝ)^1697 := by
    have hnat : (8616017 : ℕ)^2209*100000000000000^1697 ≤ 44676913174847^1697*16000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8616017 16000000 44676913174847 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962526133/5000000000 : ℝ)^2209 ≤ (11709880634853/100000000000000 : ℝ)^1697 := by
    have hnat : (962526133 : ℕ)^2209*100000000000000^1697 ≤ 11709880634853^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962526133 5000000000 11709880634853 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321560441/2500000000 : ℝ), (8616017/16000000 : ℝ), (-962526133/5000000000 : ℝ)] ![(21806603085107/50000000000000 : ℝ), (44676913174847/100000000000000 : ℝ), (11709880634853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321560441/2500000000 : ℝ)|^2209 ≤ (21806603085107/50000000000000 : ℝ)^1697
        have hw : |(1321560441/2500000000 : ℝ)|=(1321560441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8616017/16000000 : ℝ)|^2209 ≤ (44676913174847/100000000000000 : ℝ)^1697
        have hw : |(8616017/16000000 : ℝ)|=(8616017/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-962526133/5000000000 : ℝ)|^2209 ≤ (11709880634853/100000000000000 : ℝ)^1697
        have hw : |(-962526133/5000000000 : ℝ)|=(962526133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_3 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (138840939/312500000 : ℝ)*x 0 + (4227962099/10000000000 : ℝ)*x 1 + (2113981347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138840939/312500000 : ℝ)^2209 ≤ (1086965345217/3125000000000 : ℝ)^1697 := by
    have hnat : (138840939 : ℕ)^2209*3125000000000^1697 ≤ 1086965345217^1697*312500000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138840939 312500000 1086965345217 3125000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227962099/10000000000 : ℝ)^2209 ≤ (16304275741059/50000000000000 : ℝ)^1697 := by
    have hnat : (4227962099 : ℕ)^2209*50000000000000^1697 ≤ 16304275741059^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227962099 10000000000 16304275741059 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113981347/5000000000 : ℝ)^2209 ≤ (32608557455651/100000000000000 : ℝ)^1697 := by
    have hnat : (2113981347 : ℕ)^2209*100000000000000^1697 ≤ 32608557455651^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113981347 5000000000 32608557455651 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(138840939/312500000 : ℝ), (4227962099/10000000000 : ℝ), (2113981347/5000000000 : ℝ)] ![(1086965345217/3125000000000 : ℝ), (16304275741059/50000000000000 : ℝ), (32608557455651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(138840939/312500000 : ℝ)|^2209 ≤ (1086965345217/3125000000000 : ℝ)^1697
        have hw : |(138840939/312500000 : ℝ)|=(138840939/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227962099/10000000000 : ℝ)|^2209 ≤ (16304275741059/50000000000000 : ℝ)^1697
        have hw : |(4227962099/10000000000 : ℝ)|=(4227962099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113981347/5000000000 : ℝ)|^2209 ≤ (32608557455651/100000000000000 : ℝ)^1697
        have hw : |(2113981347/5000000000 : ℝ)|=(2113981347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_4 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109171863/10000000000 : ℝ)*x 0 + (5266920847/10000000000 : ℝ)*x 1 + (5266920959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109171863/10000000000 : ℝ)^2209 ≤ (6594176091361/50000000000000 : ℝ)^1697 := by
    have hnat : (2109171863 : ℕ)^2209*50000000000000^1697 ≤ 6594176091361^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109171863 10000000000 6594176091361 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266920847/10000000000 : ℝ)^2209 ≤ (2170291165103/5000000000000 : ℝ)^1697 := by
    have hnat : (5266920847 : ℕ)^2209*5000000000000^1697 ≤ 2170291165103^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266920847 10000000000 2170291165103 5000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266920959/10000000000 : ℝ)^2209 ≤ (21702912251779/50000000000000 : ℝ)^1697 := by
    have hnat : (5266920959 : ℕ)^2209*50000000000000^1697 ≤ 21702912251779^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266920959 10000000000 21702912251779 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109171863/10000000000 : ℝ), (5266920847/10000000000 : ℝ), (5266920959/10000000000 : ℝ)] ![(6594176091361/50000000000000 : ℝ), (2170291165103/5000000000000 : ℝ), (21702912251779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109171863/10000000000 : ℝ)|^2209 ≤ (6594176091361/50000000000000 : ℝ)^1697
        have hw : |(-2109171863/10000000000 : ℝ)|=(2109171863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266920847/10000000000 : ℝ)|^2209 ≤ (2170291165103/5000000000000 : ℝ)^1697
        have hw : |(5266920847/10000000000 : ℝ)|=(5266920847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266920959/10000000000 : ℝ)|^2209 ≤ (21702912251779/50000000000000 : ℝ)^1697
        have hw : |(5266920959/10000000000 : ℝ)|=(5266920959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_5 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684394659/5000000000 : ℝ)*x 0 + (-1973176957/10000000000 : ℝ)*x 1 + (52669209/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684394659/5000000000 : ℝ)^2209 ≤ (22250904041241/50000000000000 : ℝ)^1697 := by
    have hnat : (2684394659 : ℕ)^2209*50000000000000^1697 ≤ 22250904041241^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684394659 5000000000 22250904041241 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973176957/10000000000 : ℝ)^2209 ≤ (12092368024187/100000000000000 : ℝ)^1697 := by
    have hnat : (1973176957 : ℕ)^2209*100000000000000^1697 ≤ 12092368024187^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973176957 10000000000 12092368024187 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52669209/100000000 : ℝ)^2209 ≤ (21702911935313/50000000000000 : ℝ)^1697 := by
    have hnat : (52669209 : ℕ)^2209*50000000000000^1697 ≤ 21702911935313^1697*100000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52669209 100000000 21702911935313 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684394659/5000000000 : ℝ), (-1973176957/10000000000 : ℝ), (52669209/100000000 : ℝ)] ![(22250904041241/50000000000000 : ℝ), (12092368024187/100000000000000 : ℝ), (21702911935313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684394659/5000000000 : ℝ)|^2209 ≤ (22250904041241/50000000000000 : ℝ)^1697
        have hw : |(2684394659/5000000000 : ℝ)|=(2684394659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973176957/10000000000 : ℝ)|^2209 ≤ (12092368024187/100000000000000 : ℝ)^1697
        have hw : |(-1973176957/10000000000 : ℝ)|=(1973176957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52669209/100000000 : ℝ)|^2209 ≤ (21702911935313/50000000000000 : ℝ)^1697
        have hw : |(52669209/100000000 : ℝ)|=(52669209/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_6 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684394751/5000000000 : ℝ)*x 0 + (2633460429/5000000000 : ℝ)*x 1 + (-986588383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684394751/5000000000 : ℝ)^2209 ≤ (22250905033907/50000000000000 : ℝ)^1697 := by
    have hnat : (2684394751 : ℕ)^2209*50000000000000^1697 ≤ 22250905033907^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684394751 5000000000 22250905033907 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633460429/5000000000 : ℝ)^2209 ≤ (8681164684013/20000000000000 : ℝ)^1697 := by
    have hnat : (2633460429 : ℕ)^2209*20000000000000^1697 ≤ 8681164684013^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633460429 5000000000 8681164684013 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986588383/5000000000 : ℝ)^2209 ≤ (12092366500511/100000000000000 : ℝ)^1697 := by
    have hnat : (986588383 : ℕ)^2209*100000000000000^1697 ≤ 12092366500511^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986588383 5000000000 12092366500511 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684394751/5000000000 : ℝ), (2633460429/5000000000 : ℝ), (-986588383/5000000000 : ℝ)] ![(22250905033907/50000000000000 : ℝ), (8681164684013/20000000000000 : ℝ), (12092366500511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684394751/5000000000 : ℝ)|^2209 ≤ (22250905033907/50000000000000 : ℝ)^1697
        have hw : |(2684394751/5000000000 : ℝ)|=(2684394751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633460429/5000000000 : ℝ)|^2209 ≤ (8681164684013/20000000000000 : ℝ)^1697
        have hw : |(2633460429/5000000000 : ℝ)|=(2633460429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986588383/5000000000 : ℝ)|^2209 ≤ (12092366500511/100000000000000 : ℝ)^1697
        have hw : |(-986588383/5000000000 : ℝ)|=(986588383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_7 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2075177103/5000000000 : ℝ)*x 0 + (4374190257/10000000000 : ℝ)*x 1 + (4374190203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075177103/5000000000 : ℝ)^2209 ≤ (6366313975079/20000000000000 : ℝ)^1697 := by
    have hnat : (2075177103 : ℕ)^2209*20000000000000^1697 ≤ 6366313975079^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075177103 5000000000 6366313975079 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4374190257/10000000000 : ℝ)^2209 ≤ (2130263457981/6250000000000 : ℝ)^1697 := by
    have hnat : (4374190257 : ℕ)^2209*6250000000000^1697 ≤ 2130263457981^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374190257 10000000000 2130263457981 6250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4374190203/10000000000 : ℝ)^2209 ≤ (3408421477997/10000000000000 : ℝ)^1697 := by
    have hnat : (4374190203 : ℕ)^2209*10000000000000^1697 ≤ 3408421477997^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374190203 10000000000 3408421477997 10000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2075177103/5000000000 : ℝ), (4374190257/10000000000 : ℝ), (4374190203/10000000000 : ℝ)] ![(6366313975079/20000000000000 : ℝ), (2130263457981/6250000000000 : ℝ), (3408421477997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2075177103/5000000000 : ℝ)|^2209 ≤ (6366313975079/20000000000000 : ℝ)^1697
        have hw : |(2075177103/5000000000 : ℝ)|=(2075177103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4374190257/10000000000 : ℝ)|^2209 ≤ (2130263457981/6250000000000 : ℝ)^1697
        have hw : |(4374190257/10000000000 : ℝ)|=(4374190257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4374190203/10000000000 : ℝ)|^2209 ≤ (3408421477997/10000000000000 : ℝ)^1697
        have hw : |(4374190203/10000000000 : ℝ)|=(4374190203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_8 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041724549/10000000000 : ℝ)*x 0 + (5185113341/10000000000 : ℝ)*x 1 + (2699482579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041724549/10000000000 : ℝ)^2209 ≤ (1264203974263/10000000000000 : ℝ)^1697 := by
    have hnat : (2041724549 : ℕ)^2209*10000000000000^1697 ≤ 1264203974263^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041724549 10000000000 1264203974263 10000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185113341/10000000000 : ℝ)^2209 ≤ (21265141922611/50000000000000 : ℝ)^1697 := by
    have hnat : (5185113341 : ℕ)^2209*50000000000000^1697 ≤ 21265141922611^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185113341 10000000000 21265141922611 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699482579/5000000000 : ℝ)^2209 ≤ (11206919099513/25000000000000 : ℝ)^1697 := by
    have hnat : (2699482579 : ℕ)^2209*25000000000000^1697 ≤ 11206919099513^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699482579 5000000000 11206919099513 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041724549/10000000000 : ℝ), (5185113341/10000000000 : ℝ), (2699482579/5000000000 : ℝ)] ![(1264203974263/10000000000000 : ℝ), (21265141922611/50000000000000 : ℝ), (11206919099513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041724549/10000000000 : ℝ)|^2209 ≤ (1264203974263/10000000000000 : ℝ)^1697
        have hw : |(-2041724549/10000000000 : ℝ)|=(2041724549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185113341/10000000000 : ℝ)|^2209 ≤ (21265141922611/50000000000000 : ℝ)^1697
        have hw : |(5185113341/10000000000 : ℝ)|=(5185113341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699482579/5000000000 : ℝ)|^2209 ≤ (11206919099513/25000000000000 : ℝ)^1697
        have hw : |(2699482579/5000000000 : ℝ)|=(2699482579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_9 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638240847/5000000000 : ℝ)*x 0 + (-959620743/5000000000 : ℝ)*x 1 + (1349741653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638240847/5000000000 : ℝ)^2209 ≤ (43508416911473/100000000000000 : ℝ)^1697 := by
    have hnat : (2638240847 : ℕ)^2209*100000000000000^1697 ≤ 43508416911473^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638240847 5000000000 43508416911473 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959620743/5000000000 : ℝ)^2209 ≤ (11663890963393/100000000000000 : ℝ)^1697 := by
    have hnat : (959620743 : ℕ)^2209*100000000000000^1697 ≤ 11663890963393^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959620743 5000000000 11663890963393 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349741653/2500000000 : ℝ)^2209 ≤ (22413846056519/50000000000000 : ℝ)^1697 := by
    have hnat : (1349741653 : ℕ)^2209*50000000000000^1697 ≤ 22413846056519^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349741653 2500000000 22413846056519 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638240847/5000000000 : ℝ), (-959620743/5000000000 : ℝ), (1349741653/2500000000 : ℝ)] ![(43508416911473/100000000000000 : ℝ), (11663890963393/100000000000000 : ℝ), (22413846056519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638240847/5000000000 : ℝ)|^2209 ≤ (43508416911473/100000000000000 : ℝ)^1697
        have hw : |(2638240847/5000000000 : ℝ)|=(2638240847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959620743/5000000000 : ℝ)|^2209 ≤ (11663890963393/100000000000000 : ℝ)^1697
        have hw : |(-959620743/5000000000 : ℝ)|=(959620743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349741653/2500000000 : ℝ)|^2209 ≤ (22413846056519/50000000000000 : ℝ)^1697
        have hw : |(1349741653/2500000000 : ℝ)|=(1349741653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_10 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638240819/5000000000 : ℝ)*x 0 + (2699483217/5000000000 : ℝ)*x 1 + (-383848361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638240819/5000000000 : ℝ)^2209 ≤ (10877104077599/25000000000000 : ℝ)^1697 := by
    have hnat : (2638240819 : ℕ)^2209*25000000000000^1697 ≤ 10877104077599^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638240819 5000000000 10877104077599 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699483217/5000000000 : ℝ)^2209 ≤ (8965538037839/20000000000000 : ℝ)^1697 := by
    have hnat : (2699483217 : ℕ)^2209*20000000000000^1697 ≤ 8965538037839^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699483217 5000000000 8965538037839 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383848361/2000000000 : ℝ)^2209 ≤ (11663893486981/100000000000000 : ℝ)^1697 := by
    have hnat : (383848361 : ℕ)^2209*100000000000000^1697 ≤ 11663893486981^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383848361 2000000000 11663893486981 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638240819/5000000000 : ℝ), (2699483217/5000000000 : ℝ), (-383848361/2000000000 : ℝ)] ![(10877104077599/25000000000000 : ℝ), (8965538037839/20000000000000 : ℝ), (11663893486981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638240819/5000000000 : ℝ)|^2209 ≤ (10877104077599/25000000000000 : ℝ)^1697
        have hw : |(2638240819/5000000000 : ℝ)|=(2638240819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699483217/5000000000 : ℝ)|^2209 ≤ (8965538037839/20000000000000 : ℝ)^1697
        have hw : |(2699483217/5000000000 : ℝ)|=(2699483217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383848361/2000000000 : ℝ)|^2209 ≤ (11663893486981/100000000000000 : ℝ)^1697
        have hw : |(-383848361/2000000000 : ℝ)|=(383848361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_11 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1119232257/2500000000 : ℝ)*x 0 + (168426651/400000000 : ℝ)*x 1 + (4210665549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119232257/2500000000 : ℝ)^2209 ≤ (17564987199197/50000000000000 : ℝ)^1697 := by
    have hnat : (1119232257 : ℕ)^2209*50000000000000^1697 ≤ 17564987199197^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119232257 2500000000 17564987199197 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168426651/400000000 : ℝ)^2209 ≤ (32435016432973/100000000000000 : ℝ)^1697 := by
    have hnat : (168426651 : ℕ)^2209*100000000000000^1697 ≤ 32435016432973^1697*400000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168426651 400000000 32435016432973 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4210665549/10000000000 : ℝ)^2209 ≤ (8108752288317/25000000000000 : ℝ)^1697 := by
    have hnat : (4210665549 : ℕ)^2209*25000000000000^1697 ≤ 8108752288317^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210665549 10000000000 8108752288317 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119232257/2500000000 : ℝ), (168426651/400000000 : ℝ), (4210665549/10000000000 : ℝ)] ![(17564987199197/50000000000000 : ℝ), (32435016432973/100000000000000 : ℝ), (8108752288317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119232257/2500000000 : ℝ)|^2209 ≤ (17564987199197/50000000000000 : ℝ)^1697
        have hw : |(1119232257/2500000000 : ℝ)|=(1119232257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168426651/400000000 : ℝ)|^2209 ≤ (32435016432973/100000000000000 : ℝ)^1697
        have hw : |(168426651/400000000 : ℝ)|=(168426651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4210665549/10000000000 : ℝ)|^2209 ≤ (8108752288317/25000000000000 : ℝ)^1697
        have hw : |(4210665549/10000000000 : ℝ)|=(4210665549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_12 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-928412663/5000000000 : ℝ)*x 0 + (1092970109/2000000000 : ℝ)*x 1 + (5255781121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928412663/5000000000 : ℝ)^2209 ≤ (2234512385637/20000000000000 : ℝ)^1697 := by
    have hnat : (928412663 : ℕ)^2209*20000000000000^1697 ≤ 2234512385637^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928412663 5000000000 2234512385637 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092970109/2000000000 : ℝ)^2209 ≤ (45541079827503/100000000000000 : ℝ)^1697 := by
    have hnat : (1092970109 : ℕ)^2209*100000000000000^1697 ≤ 45541079827503^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092970109 2000000000 45541079827503 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255781121/10000000000 : ℝ)^2209 ≤ (10821589558747/25000000000000 : ℝ)^1697 := by
    have hnat : (5255781121 : ℕ)^2209*25000000000000^1697 ≤ 10821589558747^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255781121 10000000000 10821589558747 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928412663/5000000000 : ℝ), (1092970109/2000000000 : ℝ), (5255781121/10000000000 : ℝ)] ![(2234512385637/20000000000000 : ℝ), (45541079827503/100000000000000 : ℝ), (10821589558747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928412663/5000000000 : ℝ)|^2209 ≤ (2234512385637/20000000000000 : ℝ)^1697
        have hw : |(-928412663/5000000000 : ℝ)|=(928412663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092970109/2000000000 : ℝ)|^2209 ≤ (45541079827503/100000000000000 : ℝ)^1697
        have hw : |(1092970109/2000000000 : ℝ)|=(1092970109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255781121/10000000000 : ℝ)|^2209 ≤ (10821589558747/25000000000000 : ℝ)^1697
        have hw : |(5255781121/10000000000 : ℝ)|=(5255781121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_13 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2688287333/5000000000 : ℝ)*x 0 + (-988808979/5000000000 : ℝ)*x 1 + (1313945399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688287333/5000000000 : ℝ)^2209 ≤ (22292914571641/50000000000000 : ℝ)^1697 := by
    have hnat : (2688287333 : ℕ)^2209*50000000000000^1697 ≤ 22292914571641^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688287333 5000000000 22292914571641 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988808979/5000000000 : ℝ)^2209 ≤ (2425561502091/20000000000000 : ℝ)^1697 := by
    have hnat : (988808979 : ℕ)^2209*20000000000000^1697 ≤ 2425561502091^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988808979 5000000000 2425561502091 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313945399/2500000000 : ℝ)^2209 ≤ (43286363327373/100000000000000 : ℝ)^1697 := by
    have hnat : (1313945399 : ℕ)^2209*100000000000000^1697 ≤ 43286363327373^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313945399 2500000000 43286363327373 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688287333/5000000000 : ℝ), (-988808979/5000000000 : ℝ), (1313945399/2500000000 : ℝ)] ![(22292914571641/50000000000000 : ℝ), (2425561502091/20000000000000 : ℝ), (43286363327373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688287333/5000000000 : ℝ)|^2209 ≤ (22292914571641/50000000000000 : ℝ)^1697
        have hw : |(2688287333/5000000000 : ℝ)|=(2688287333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-988808979/5000000000 : ℝ)|^2209 ≤ (2425561502091/20000000000000 : ℝ)^1697
        have hw : |(-988808979/5000000000 : ℝ)|=(988808979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313945399/2500000000 : ℝ)|^2209 ≤ (43286363327373/100000000000000 : ℝ)^1697
        have hw : |(1313945399/2500000000 : ℝ)|=(1313945399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_14 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2688287403/5000000000 : ℝ)*x 0 + (5255781109/10000000000 : ℝ)*x 1 + (-1977618423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688287403/5000000000 : ℝ)^2209 ≤ (44585830654521/100000000000000 : ℝ)^1697 := by
    have hnat : (2688287403 : ℕ)^2209*100000000000000^1697 ≤ 44585830654521^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688287403 5000000000 44585830654521 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255781109/10000000000 : ℝ)^2209 ≤ (21643179053169/50000000000000 : ℝ)^1697 := by
    have hnat : (5255781109 : ℕ)^2209*50000000000000^1697 ≤ 21643179053169^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255781109 10000000000 21643179053169 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977618423/10000000000 : ℝ)^2209 ≤ (2425562244489/20000000000000 : ℝ)^1697 := by
    have hnat : (1977618423 : ℕ)^2209*20000000000000^1697 ≤ 2425562244489^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977618423 10000000000 2425562244489 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688287403/5000000000 : ℝ), (5255781109/10000000000 : ℝ), (-1977618423/10000000000 : ℝ)] ![(44585830654521/100000000000000 : ℝ), (21643179053169/50000000000000 : ℝ), (2425562244489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688287403/5000000000 : ℝ)|^2209 ≤ (44585830654521/100000000000000 : ℝ)^1697
        have hw : |(2688287403/5000000000 : ℝ)|=(2688287403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255781109/10000000000 : ℝ)|^2209 ≤ (21643179053169/50000000000000 : ℝ)^1697
        have hw : |(5255781109/10000000000 : ℝ)|=(5255781109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977618423/10000000000 : ℝ)|^2209 ≤ (2425562244489/20000000000000 : ℝ)^1697
        have hw : |(-1977618423/10000000000 : ℝ)|=(1977618423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_box_15 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4122308483/10000000000 : ℝ)*x 0 + (4387972183/10000000000 : ℝ)*x 1 + (4387971757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4122308483/10000000000 : ℝ)^2209 ≤ (31551858731339/100000000000000 : ℝ)^1697 := by
    have hnat : (4122308483 : ℕ)^2209*100000000000000^1697 ≤ 31551858731339^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122308483 10000000000 31551858731339 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387972183/10000000000 : ℝ)^2209 ≤ (34224072788753/100000000000000 : ℝ)^1697 := by
    have hnat : (4387972183 : ℕ)^2209*100000000000000^1697 ≤ 34224072788753^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387972183 10000000000 34224072788753 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4387971757/10000000000 : ℝ)^2209 ≤ (17112034231851/50000000000000 : ℝ)^1697 := by
    have hnat : (4387971757 : ℕ)^2209*50000000000000^1697 ≤ 17112034231851^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387971757 10000000000 17112034231851 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4122308483/10000000000 : ℝ), (4387972183/10000000000 : ℝ), (4387971757/10000000000 : ℝ)] ![(31551858731339/100000000000000 : ℝ), (34224072788753/100000000000000 : ℝ), (17112034231851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4122308483/10000000000 : ℝ)|^2209 ≤ (31551858731339/100000000000000 : ℝ)^1697
        have hw : |(4122308483/10000000000 : ℝ)|=(4122308483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4387972183/10000000000 : ℝ)|^2209 ≤ (34224072788753/100000000000000 : ℝ)^1697
        have hw : |(4387972183/10000000000 : ℝ)|=(4387972183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4387971757/10000000000 : ℝ)|^2209 ≤ (17112034231851/50000000000000 : ℝ)^1697
        have hw : |(4387971757/10000000000 : ℝ)|=(4387971757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1458_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31459/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14793/25000 : ℝ) ∧ (80607/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84793/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5699/50000 : ℝ) ^ (4417/1024 : ℝ) ≤ (1708765607691323/20000000000000000000 : ℝ) := by
    have hpowers : (5699/50000 : ℝ)^4417 ≤ (1708765607691323/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5699 : ℕ)^4417*20000000000000000000^1024 ≤ 1708765607691323^1024*50000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5699 50000 1708765607691323 20000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5699/50000 : ℝ)) (X := (1708765607691323/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (4417/1024 : ℝ) ≤ (26137801929495723/100000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^4417 ≤ (26137801929495723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14771 : ℕ)^4417*100000000000000000000^1024 ≤ 26137801929495723^1024*100000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 26137801929495723 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (26137801929495723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001708765607691323/10000000000000000000 : ℝ) ≤ (5000198059899741/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (10001708765607691323/10000000000000000000 : ℝ)^1024 ≤ (5000198059899741/5000000000000000 : ℝ)^4417 := by
      have hnat : (10001708765607691323 : ℕ)^1024*5000000000000000^4417 ≤ 5000198059899741^4417*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001708765607691323 10000000000000000000 5000198059899741 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000198059899741/5000000000000000 : ℝ)) (X := (10001708765607691323/10000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017340814983976169/50000000000000000000 : ℝ) ≤ (2500200980639313/2500000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50017340814983976169/50000000000000000000 : ℝ)^1024 ≤ (2500200980639313/2500000000000000 : ℝ)^4417 := by
      have hnat : (50017340814983976169 : ℕ)^1024*2500000000000000^4417 ≤ 2500200980639313^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017340814983976169 50000000000000000000 2500200980639313 2500000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500200980639313/2500000000000000 : ℝ)) (X := (50017340814983976169/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026137801929495723/50000000000000000000 : ℝ) ≤ (5000605862657511/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50026137801929495723/50000000000000000000 : ℝ)^1024 ≤ (5000605862657511/5000000000000000 : ℝ)^4417 := by
      have hnat : (50026137801929495723 : ℕ)^1024*5000000000000000^4417 ≤ 5000605862657511^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026137801929495723 50000000000000000000 5000605862657511 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000605862657511/5000000000000000 : ℝ)) (X := (50026137801929495723/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1708765607691323/20000000000000000000 : ℝ) ≤ ((16861019920208763933/16865000000000000000 : ℝ)+2*(40780275777/33730000000000 : ℝ)*(5699/50000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (16861019920208763933/16865000000000000000 : ℝ)+2*(40780275777/33730000000000 : ℝ)*(5699/50000 : ℝ)=(5000198059899741/5000000000000000 : ℝ) by norm_num, show 1+2*(1708765607691323/20000000000000000000 : ℝ)=(10001708765607691323/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26137801929495723/100000000000000000000 : ℝ)+(1708765607691323/20000000000000000000 : ℝ) ≤ ((16861019920208763933/16865000000000000000 : ℝ)+(40780275777/33730000000000 : ℝ)*((14771/100000 : ℝ)+(5699/50000 : ℝ)))^(4417/1024 : ℝ) := by
    rw [show (16861019920208763933/16865000000000000000 : ℝ)+(40780275777/33730000000000 : ℝ)*((14771/100000 : ℝ)+(5699/50000 : ℝ))=(2500200980639313/2500000000000000 : ℝ) by norm_num, show 1+(26137801929495723/100000000000000000000 : ℝ)+(1708765607691323/20000000000000000000 : ℝ)=(50017340814983976169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26137801929495723/100000000000000000000 : ℝ) ≤ ((16861019920208763933/16865000000000000000 : ℝ)+2*(40780275777/33730000000000 : ℝ)*(14771/100000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (16861019920208763933/16865000000000000000 : ℝ)+2*(40780275777/33730000000000 : ℝ)*(14771/100000 : ℝ)=(5000605862657511/5000000000000000 : ℝ) by norm_num, show 1+2*(26137801929495723/100000000000000000000 : ℝ)=(50026137801929495723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16861019920208763933/16865000000000000000 : ℝ)*(X 1 0+X 2 0)+(40780275777/33730000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16861019920208763933/16865000000000000000 : ℝ)) (alpha := (40780275777/33730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16861019920208763933/16865000000000000000 : ℝ)*(X 0 1+X 2 1)+(40780275777/33730000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16861019920208763933/16865000000000000000 : ℝ)) (alpha := (40780275777/33730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16861019920208763933/16865000000000000000 : ℝ)*(X 0 2+X 1 2)+(40780275777/33730000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16861019920208763933/16865000000000000000 : ℝ)) (alpha := (40780275777/33730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1789245413/10000000000 : ℝ)*X 0 0+(13462527/25000000 : ℝ)*X 0 1+(673126241/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286241751/10000000000 : ℝ)*X 1 0+(-385010683/2000000000 : ℝ)*X 1 1+(1346252449/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321560441/2500000000 : ℝ)*X 2 0+(8616017/16000000 : ℝ)*X 2 1+(-962526133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((138840939/312500000 : ℝ)*X 0 0+(4227962099/10000000000 : ℝ)*X 0 1+(2113981347/5000000000 : ℝ)*X 0 2+(138840939/312500000 : ℝ)*X 1 0+(4227962099/10000000000 : ℝ)*X 1 1+(2113981347/5000000000 : ℝ)*X 1 2+(138840939/312500000 : ℝ)*X 2 0+(4227962099/10000000000 : ℝ)*X 2 1+(2113981347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109171863/10000000000 : ℝ)*X 0 0+(5266920847/10000000000 : ℝ)*X 0 1+(5266920959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684394659/5000000000 : ℝ)*X 1 0+(-1973176957/10000000000 : ℝ)*X 1 1+(52669209/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684394751/5000000000 : ℝ)*X 2 0+(2633460429/5000000000 : ℝ)*X 2 1+(-986588383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2075177103/5000000000 : ℝ)*X 0 0+(4374190257/10000000000 : ℝ)*X 0 1+(4374190203/10000000000 : ℝ)*X 0 2+(2075177103/5000000000 : ℝ)*X 1 0+(4374190257/10000000000 : ℝ)*X 1 1+(4374190203/10000000000 : ℝ)*X 1 2+(2075177103/5000000000 : ℝ)*X 2 0+(4374190257/10000000000 : ℝ)*X 2 1+(4374190203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2041724549/10000000000 : ℝ)*X 0 0+(5185113341/10000000000 : ℝ)*X 0 1+(2699482579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638240847/5000000000 : ℝ)*X 1 0+(-959620743/5000000000 : ℝ)*X 1 1+(1349741653/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638240819/5000000000 : ℝ)*X 2 0+(2699483217/5000000000 : ℝ)*X 2 1+(-383848361/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1119232257/2500000000 : ℝ)*X 0 0+(168426651/400000000 : ℝ)*X 0 1+(4210665549/10000000000 : ℝ)*X 0 2+(1119232257/2500000000 : ℝ)*X 1 0+(168426651/400000000 : ℝ)*X 1 1+(4210665549/10000000000 : ℝ)*X 1 2+(1119232257/2500000000 : ℝ)*X 2 0+(168426651/400000000 : ℝ)*X 2 1+(4210665549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-928412663/5000000000 : ℝ)*X 0 0+(1092970109/2000000000 : ℝ)*X 0 1+(5255781121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688287333/5000000000 : ℝ)*X 1 0+(-988808979/5000000000 : ℝ)*X 1 1+(1313945399/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688287403/5000000000 : ℝ)*X 2 0+(5255781109/10000000000 : ℝ)*X 2 1+(-1977618423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4122308483/10000000000 : ℝ)*X 0 0+(4387972183/10000000000 : ℝ)*X 0 1+(4387971757/10000000000 : ℝ)*X 0 2+(4122308483/10000000000 : ℝ)*X 1 0+(4387972183/10000000000 : ℝ)*X 1 1+(4387971757/10000000000 : ℝ)*X 1 2+(4122308483/10000000000 : ℝ)*X 2 0+(4387972183/10000000000 : ℝ)*X 2 1+(4387971757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31459/50000 : ℝ) ≤ (-132634429320858749391912721137969/210812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32155447/100000000000000 : ℝ)*(upper0) + (4206847/4000000000000 : ℝ)*(lower2) + (3534651/50000000000000 : ℝ)*(lower3) + (14717701/100000000000000 : ℝ)*(upper5) + (1524103190802169/50000000000000 : ℝ)*(major0) + (1524103190802169/50000000000000 : ℝ)*(major1) + (1524103190802169/50000000000000 : ℝ)*(major2) + (1501819803/100000000000000 : ℝ)*(sp1) + (186621729/10000000000000 : ℝ)*(sp3) + (131377787439533/3125000000000 : ℝ)*(sp4) + (2102043848122627/50000000000000 : ℝ)*(sp5) + (2102034696543691/50000000000000 : ℝ)*(sp6) + (239161705187627/12500000000000 : ℝ)*(sp7) + (792199107/4000000000000 : ℝ)*(sp14) + (956647753859153/50000000000000 : ℝ)*(f.failure) + (131377787439533/3125000000000 : ℝ)*(f.sum) + (5110554778243/843250000000000000000000000 : ℝ)*base66 + (3629618917553629323/843250000000000000000000000000000 : ℝ)*base68 + (5408723753887129323/843250000000000000000000000000000 : ℝ)*base70 + (6381632572941379323/843250000000000000000000000000000 : ℝ)*base72 + (361212272487/26984000000000000000000000 : ℝ)*base74 + (9716289367220129323/843250000000000000000000000000000 : ℝ)*base76 + (10738813249665629323/843250000000000000000000000000000 : ℝ)*base78 + (24875997965364620677/843250000000000000000000000000000 : ℝ)*base79 + (7138233593869/3373000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3522501/312500000000000000000 : ℝ)*base89 + (3522501/312500000000000000000 : ℝ)*base91 + (3522501/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14793/25000 : ℝ) ≤ (1995945193264287563660456949/3373000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68433203/20000000000000 : ℝ)*(lower1) + (19793921/10000000000000 : ℝ)*(lower2) + (15907419/6250000000000 : ℝ)*(upper4) + (1560403594400953/50000000000000 : ℝ)*(major0) + (1560403594400953/50000000000000 : ℝ)*(major1) + (1560403594400953/50000000000000 : ℝ)*(major2) + (2131504692795669/50000000000000 : ℝ)*(sp0) + (85254478163257/2000000000000 : ℝ)*(sp1) + (2131502743948059/50000000000000 : ℝ)*(sp2) + (1958860930324629/100000000000000 : ℝ)*(sp3) + (466083493/2500000000000 : ℝ)*(sp6) + (4588370007/100000000000000 : ℝ)*(sp7) + (29491289/200000000000 : ℝ)*(sp8) + (300223072987/100000000000000 : ℝ)*(sp9) + (489716379673659/25000000000000 : ℝ)*(f.failure) + (2131512065617919/50000000000000 : ℝ)*(f.sum) + (5177831407063/421625000000000000000000000 : ℝ)*base65 + (6803690891984771851/843250000000000000000000000000000 : ℝ)*base68 + (8034990747258021851/843250000000000000000000000000000 : ℝ)*base70 + (8415420878011228149/843250000000000000000000000000000 : ℝ)*base71 + (281053371361/67460000000000000000000000 : ℝ)*base74 + (2564447584106978149/843250000000000000000000000000000 : ℝ)*base75 + (2755407757143228149/843250000000000000000000000000000 : ℝ)*base77 + (7026653452367271851/843250000000000000000000000000000 : ℝ)*base80 + (6459568471377/3373000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1087903/156250000000000000000 : ℝ)*base89 + (1087903/156250000000000000000 : ℝ)*base91 + (1087903/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80607/100000 : ℝ) ≤ (679737628299975521656580956463943/843250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4132493/2500000000000 : ℝ)*(upper0) + (235663153/100000000000000 : ℝ)*(upper1) + (3276909/6250000000000 : ℝ)*(upper2) + (54813441/25000000000000 : ℝ)*(upper3) + (3427041126716219/100000000000000 : ℝ)*(major0) + (3427041126716219/100000000000000 : ℝ)*(major1) + (3427041126716219/100000000000000 : ℝ)*(major2) + (498909449483/100000000000000 : ℝ)*(sp1) + (472016706313/100000000000000 : ℝ)*(sp2) + (78584989541/50000000000000 : ℝ)*(sp3) + (4676130330169251/100000000000000 : ℝ)*(sp8) + (584453927589971/12500000000000 : ℝ)*(sp9) + (4675658313462937/100000000000000 : ℝ)*(sp10) + (2150924998237153/100000000000000 : ℝ)*(sp11) + (1075541084108117/50000000000000 : ℝ)*(f.failure) + (4676130330169251/100000000000000 : ℝ)*(f.sum) + (22503690715707/3373000000000000000000000000 : ℝ)*base66 + (16309207681881170673/1686500000000000000000000000000000 : ℝ)*base68 + (21382300499164670673/1686500000000000000000000000000000 : ℝ)*base70 + (15735425236907670673/1686500000000000000000000000000000 : ℝ)*base72 + (12589489593087/1686500000000000000000000000 : ℝ)*base74 + (26392158078213670673/1686500000000000000000000000000000 : ℝ)*base76 + (14320814693632170673/1686500000000000000000000000000000 : ℝ)*base78 + (19728678669939170673/1686500000000000000000000000000000 : ℝ)*base80 + (199736774227/33730000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1132911/312500000000000000000 : ℝ)*base90 + (1132911/312500000000000000000 : ℝ)*base92 + (1132911/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84793/100000 : ℝ) ≤ (-714994762887193464057640366191777/843250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263304719/100000000000000 : ℝ)*(upper3) + (6092111/10000000000000 : ℝ)*(lower4) + (2121563/10000000000000 : ℝ)*(upper5) + (3464829229450377/100000000000000 : ℝ)*(major0) + (3464829229450377/100000000000000 : ℝ)*(major1) + (3464829229450377/100000000000000 : ℝ)*(major2) + (11570347981/100000000000000 : ℝ)*(sp0) + (166642998127/100000000000000 : ℝ)*(sp5) + (330908305619/100000000000000 : ℝ)*(sp6) + (4090966521/25000000000000 : ℝ)*(sp7) + (2391554686278179/50000000000000 : ℝ)*(sp12) + (4782954299906213/100000000000000 : ℝ)*(sp13) + (4782790034598721/100000000000000 : ℝ)*(sp14) + (2174784607526597/100000000000000 : ℝ)*(sp15) + (2174800971392681/100000000000000 : ℝ)*(f.failure) + (239156047145217/5000000000000 : ℝ)*(f.sum) + (509599674163/421625000000000000000000000 : ℝ)*base66 + (6639789440093147259/1686500000000000000000000000000000 : ℝ)*base68 + (10955863212199852741/1686500000000000000000000000000000 : ℝ)*base69 + (10709616955931852741/1686500000000000000000000000000000 : ℝ)*base71 + (24661037199/33730000000000000000000000 : ℝ)*base74 + (10266947486113147259/1686500000000000000000000000000000 : ℝ)*base76 + (4165022325198147259/1686500000000000000000000000000000 : ℝ)*base78 + (16546885405249647259/1686500000000000000000000000000000 : ℝ)*base80 + (5883727529523/1686500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (53123/625000000000000000000 : ℝ)*base90 + (53123/625000000000000000000 : ℝ)*base92 + (53123/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1458_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31459/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14793/25000 : ℝ) else (80607/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84793/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1458_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1458_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31459/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14793/25000 : ℝ) else (80607/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84793/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1458_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1458_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31459/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14793/25000 : ℝ) else (80607/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84793/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1458_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
