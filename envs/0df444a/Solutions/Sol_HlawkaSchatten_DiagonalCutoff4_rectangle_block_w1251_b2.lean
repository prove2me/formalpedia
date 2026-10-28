-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:50.856411+00:00
-- url     : https://prove2.me/submissions/bd3d112e-30dc-4866-969e-0772aebf6ed5

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
theorem support_rectangle_w1251_s6_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115810717/10000000000 : ℝ)*x 0 + (13478037/25000000 : ℝ)*x 1 + (2633579089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115810717/10000000000 : ℝ)^2111 ≤ (12867506716457/100000000000000 : ℝ)^1599 := by
    have hnat : (2115810717 : ℕ)^2111*100000000000000^1599 ≤ 12867506716457^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115810717 10000000000 12867506716457 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13478037/25000000 : ℝ)^2111 ≤ (1382364856851/3125000000000 : ℝ)^1599 := by
    have hnat : (13478037 : ℕ)^2111*3125000000000^1599 ≤ 1382364856851^1599*25000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13478037 25000000 1382364856851 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633579089/5000000000 : ℝ)^2111 ≤ (42896817850121/100000000000000 : ℝ)^1599 := by
    have hnat : (2633579089 : ℕ)^2111*100000000000000^1599 ≤ 42896817850121^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633579089 5000000000 42896817850121 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115810717/10000000000 : ℝ), (13478037/25000000 : ℝ), (2633579089/5000000000 : ℝ)] ![(12867506716457/100000000000000 : ℝ), (1382364856851/3125000000000 : ℝ), (42896817850121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115810717/10000000000 : ℝ)|^2111 ≤ (12867506716457/100000000000000 : ℝ)^1599
        have hw : |(-2115810717/10000000000 : ℝ)|=(2115810717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13478037/25000000 : ℝ)|^2111 ≤ (1382364856851/3125000000000 : ℝ)^1599
        have hw : |(13478037/25000000 : ℝ)|=(13478037/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633579089/5000000000 : ℝ)|^2111 ≤ (42896817850121/100000000000000 : ℝ)^1599
        have hw : |(2633579089/5000000000 : ℝ)|=(2633579089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344307581/10000000000 : ℝ)*x 0 + (-1089355443/5000000000 : ℝ)*x 1 + (1053431663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344307581/10000000000 : ℝ)^2111 ≤ (43728265563291/100000000000000 : ℝ)^1599 := by
    have hnat : (5344307581 : ℕ)^2111*100000000000000^1599 ≤ 43728265563291^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344307581 10000000000 43728265563291 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089355443/5000000000 : ℝ)^2111 ≤ (6687457544979/50000000000000 : ℝ)^1599 := by
    have hnat : (1089355443 : ℕ)^2111*50000000000000^1599 ≤ 6687457544979^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089355443 5000000000 6687457544979 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053431663/2000000000 : ℝ)^2111 ≤ (21448409661571/50000000000000 : ℝ)^1599 := by
    have hnat : (1053431663 : ℕ)^2111*50000000000000^1599 ≤ 21448409661571^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053431663 2000000000 21448409661571 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344307581/10000000000 : ℝ), (-1089355443/5000000000 : ℝ), (1053431663/2000000000 : ℝ)] ![(43728265563291/100000000000000 : ℝ), (6687457544979/50000000000000 : ℝ), (21448409661571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344307581/10000000000 : ℝ)|^2111 ≤ (43728265563291/100000000000000 : ℝ)^1599
        have hw : |(5344307581/10000000000 : ℝ)|=(5344307581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089355443/5000000000 : ℝ)|^2111 ≤ (6687457544979/50000000000000 : ℝ)^1599
        have hw : |(-1089355443/5000000000 : ℝ)|=(1089355443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053431663/2000000000 : ℝ)|^2111 ≤ (21448409661571/50000000000000 : ℝ)^1599
        have hw : |(1053431663/2000000000 : ℝ)|=(1053431663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344307397/10000000000 : ℝ)*x 0 + (1316789579/2500000000 : ℝ)*x 1 + (-544677783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344307397/10000000000 : ℝ)^2111 ≤ (21864131787847/50000000000000 : ℝ)^1599 := by
    have hnat : (5344307397 : ℕ)^2111*50000000000000^1599 ≤ 21864131787847^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344307397 10000000000 21864131787847 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316789579/2500000000 : ℝ)^2111 ≤ (21448409666947/50000000000000 : ℝ)^1599 := by
    have hnat : (1316789579 : ℕ)^2111*50000000000000^1599 ≤ 21448409666947^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316789579 2500000000 21448409666947 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544677783/2500000000 : ℝ)^2111 ≤ (1671864635461/12500000000000 : ℝ)^1599 := by
    have hnat : (544677783 : ℕ)^2111*12500000000000^1599 ≤ 1671864635461^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544677783 2500000000 1671864635461 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344307397/10000000000 : ℝ), (1316789579/2500000000 : ℝ), (-544677783/2500000000 : ℝ)] ![(21864131787847/50000000000000 : ℝ), (21448409666947/50000000000000 : ℝ), (1671864635461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344307397/10000000000 : ℝ)|^2111 ≤ (21864131787847/50000000000000 : ℝ)^1599
        have hw : |(5344307397/10000000000 : ℝ)|=(5344307397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316789579/2500000000 : ℝ)|^2111 ≤ (21448409666947/50000000000000 : ℝ)^1599
        have hw : |(1316789579/2500000000 : ℝ)|=(1316789579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544677783/2500000000 : ℝ)|^2111 ≤ (1671864635461/12500000000000 : ℝ)^1599
        have hw : |(-544677783/2500000000 : ℝ)|=(544677783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4349530823/10000000000 : ℝ)*x 0 + (264078503/625000000 : ℝ)*x 1 + (2238675363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349530823/10000000000 : ℝ)^2111 ≤ (33317440298927/100000000000000 : ℝ)^1599 := by
    have hnat : (4349530823 : ℕ)^2111*100000000000000^1599 ≤ 33317440298927^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349530823 10000000000 33317440298927 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264078503/625000000 : ℝ)^2111 ≤ (32066467960937/100000000000000 : ℝ)^1599 := by
    have hnat : (264078503 : ℕ)^2111*100000000000000^1599 ≤ 32066467960937^1599*625000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264078503 625000000 32066467960937 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238675363/5000000000 : ℝ)^2111 ≤ (1384643669051/4000000000000 : ℝ)^1599 := by
    have hnat : (2238675363 : ℕ)^2111*4000000000000^1599 ≤ 1384643669051^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238675363 5000000000 1384643669051 4000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349530823/10000000000 : ℝ), (264078503/625000000 : ℝ), (2238675363/5000000000 : ℝ)] ![(33317440298927/100000000000000 : ℝ), (32066467960937/100000000000000 : ℝ), (1384643669051/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349530823/10000000000 : ℝ)|^2111 ≤ (33317440298927/100000000000000 : ℝ)^1599
        have hw : |(4349530823/10000000000 : ℝ)|=(4349530823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264078503/625000000 : ℝ)|^2111 ≤ (32066467960937/100000000000000 : ℝ)^1599
        have hw : |(264078503/625000000 : ℝ)|=(264078503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238675363/5000000000 : ℝ)|^2111 ≤ (1384643669051/4000000000000 : ℝ)^1599
        have hw : |(2238675363/5000000000 : ℝ)|=(2238675363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-528953943/2500000000 : ℝ)*x 0 + (526747167/1000000000 : ℝ)*x 1 + (1347724971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528953943/2500000000 : ℝ)^2111 ≤ (3216886825671/25000000000000 : ℝ)^1599 := by
    have hnat : (528953943 : ℕ)^2111*25000000000000^1599 ≤ 3216886825671^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528953943 2500000000 3216886825671 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526747167/1000000000 : ℝ)^2111 ≤ (8580037708449/20000000000000 : ℝ)^1599 := by
    have hnat : (526747167 : ℕ)^2111*20000000000000^1599 ≤ 8580037708449^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526747167 1000000000 8580037708449 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347724971/2500000000 : ℝ)^2111 ≤ (2764516509147/6250000000000 : ℝ)^1599 := by
    have hnat : (1347724971 : ℕ)^2111*6250000000000^1599 ≤ 2764516509147^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347724971 2500000000 2764516509147 6250000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528953943/2500000000 : ℝ), (526747167/1000000000 : ℝ), (1347724971/2500000000 : ℝ)] ![(3216886825671/25000000000000 : ℝ), (8580037708449/20000000000000 : ℝ), (2764516509147/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528953943/2500000000 : ℝ)|^2111 ≤ (3216886825671/25000000000000 : ℝ)^1599
        have hw : |(-528953943/2500000000 : ℝ)|=(528953943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526747167/1000000000 : ℝ)|^2111 ≤ (8580037708449/20000000000000 : ℝ)^1599
        have hw : |(526747167/1000000000 : ℝ)|=(526747167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347724971/2500000000 : ℝ)|^2111 ≤ (2764516509147/6250000000000 : ℝ)^1599
        have hw : |(1347724971/2500000000 : ℝ)|=(1347724971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656317649/5000000000 : ℝ)*x 0 + (-2054969359/10000000000 : ℝ)*x 1 + (2695449687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656317649/5000000000 : ℝ)^2111 ≤ (43386461570557/100000000000000 : ℝ)^1599 := by
    have hnat : (2656317649 : ℕ)^2111*100000000000000^1599 ≤ 43386461570557^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656317649 5000000000 43386461570557 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054969359/10000000000 : ℝ)^2111 ≤ (3095319948447/25000000000000 : ℝ)^1599 := by
    have hnat : (2054969359 : ℕ)^2111*25000000000000^1599 ≤ 3095319948447^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054969359 10000000000 3095319948447 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695449687/5000000000 : ℝ)^2111 ≤ (44232258621917/100000000000000 : ℝ)^1599 := by
    have hnat : (2695449687 : ℕ)^2111*100000000000000^1599 ≤ 44232258621917^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695449687 5000000000 44232258621917 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656317649/5000000000 : ℝ), (-2054969359/10000000000 : ℝ), (2695449687/5000000000 : ℝ)] ![(43386461570557/100000000000000 : ℝ), (3095319948447/25000000000000 : ℝ), (44232258621917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656317649/5000000000 : ℝ)|^2111 ≤ (43386461570557/100000000000000 : ℝ)^1599
        have hw : |(2656317649/5000000000 : ℝ)|=(2656317649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054969359/10000000000 : ℝ)|^2111 ≤ (3095319948447/25000000000000 : ℝ)^1599
        have hw : |(-2054969359/10000000000 : ℝ)|=(2054969359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695449687/5000000000 : ℝ)|^2111 ≤ (44232258621917/100000000000000 : ℝ)^1599
        have hw : |(2695449687/5000000000 : ℝ)|=(2695449687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_6 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656317761/5000000000 : ℝ)*x 0 + (5390899003/10000000000 : ℝ)*x 1 + (-51374239/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656317761/5000000000 : ℝ)^2111 ≤ (1084661599641/2500000000000 : ℝ)^1599 := by
    have hnat : (2656317761 : ℕ)^2111*2500000000000^1599 ≤ 1084661599641^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656317761 5000000000 1084661599641 2500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390899003/10000000000 : ℝ)^2111 ≤ (22116127301581/50000000000000 : ℝ)^1599 := by
    have hnat : (5390899003 : ℕ)^2111*50000000000000^1599 ≤ 22116127301581^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390899003 10000000000 22116127301581 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51374239/250000000 : ℝ)^2111 ≤ (2476256278519/20000000000000 : ℝ)^1599 := by
    have hnat : (51374239 : ℕ)^2111*20000000000000^1599 ≤ 2476256278519^1599*250000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51374239 250000000 2476256278519 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656317761/5000000000 : ℝ), (5390899003/10000000000 : ℝ), (-51374239/250000000 : ℝ)] ![(1084661599641/2500000000000 : ℝ), (22116127301581/50000000000000 : ℝ), (2476256278519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656317761/5000000000 : ℝ)|^2111 ≤ (1084661599641/2500000000000 : ℝ)^1599
        have hw : |(2656317761/5000000000 : ℝ)|=(2656317761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390899003/10000000000 : ℝ)|^2111 ≤ (22116127301581/50000000000000 : ℝ)^1599
        have hw : |(5390899003/10000000000 : ℝ)|=(5390899003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51374239/250000000 : ℝ)|^2111 ≤ (2476256278519/20000000000000 : ℝ)^1599
        have hw : |(-51374239/250000000 : ℝ)|=(51374239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_7 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2174770323/5000000000 : ℝ)*x 0 + (447671283/1000000000 : ℝ)*x 1 + (2112947973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174770323/5000000000 : ℝ)^2111 ≤ (33317539636441/100000000000000 : ℝ)^1599 := by
    have hnat : (2174770323 : ℕ)^2111*100000000000000^1599 ≤ 33317539636441^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174770323 5000000000 33317539636441 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447671283/1000000000 : ℝ)^2111 ≤ (17304790445863/50000000000000 : ℝ)^1599 := by
    have hnat : (447671283 : ℕ)^2111*50000000000000^1599 ≤ 17304790445863^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447671283 1000000000 17304790445863 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112947973/5000000000 : ℝ)^2111 ≤ (32072879453547/100000000000000 : ℝ)^1599 := by
    have hnat : (2112947973 : ℕ)^2111*100000000000000^1599 ≤ 32072879453547^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112947973 5000000000 32072879453547 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174770323/5000000000 : ℝ), (447671283/1000000000 : ℝ), (2112947973/5000000000 : ℝ)] ![(33317539636441/100000000000000 : ℝ), (17304790445863/50000000000000 : ℝ), (32072879453547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174770323/5000000000 : ℝ)|^2111 ≤ (33317539636441/100000000000000 : ℝ)^1599
        have hw : |(2174770323/5000000000 : ℝ)|=(2174770323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447671283/1000000000 : ℝ)|^2111 ≤ (17304790445863/50000000000000 : ℝ)^1599
        have hw : |(447671283/1000000000 : ℝ)|=(447671283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112947973/5000000000 : ℝ)|^2111 ≤ (32072879453547/100000000000000 : ℝ)^1599
        have hw : |(2112947973/5000000000 : ℝ)|=(2112947973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s6_8 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-38179669/10000000000 : ℝ)*x 0 + (5912456931/10000000000 : ℝ)*x 1 + (2956259669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38179669/10000000000 : ℝ)^2111 ≤ (2567996959/4000000000000 : ℝ)^1599 := by
    have hnat : (38179669 : ℕ)^2111*4000000000000^1599 ≤ 2567996959^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38179669 10000000000 2567996959 4000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5912456931/10000000000 : ℝ)^2111 ≤ (49967551880947/100000000000000 : ℝ)^1599 := by
    have hnat : (5912456931 : ℕ)^2111*100000000000000^1599 ≤ 49967551880947^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912456931 10000000000 49967551880947 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956259669/5000000000 : ℝ)^2111 ≤ (49968248176933/100000000000000 : ℝ)^1599 := by
    have hnat : (2956259669 : ℕ)^2111*100000000000000^1599 ≤ 49968248176933^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956259669 5000000000 49968248176933 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38179669/10000000000 : ℝ), (5912456931/10000000000 : ℝ), (2956259669/5000000000 : ℝ)] ![(2567996959/4000000000000 : ℝ), (49967551880947/100000000000000 : ℝ), (49968248176933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38179669/10000000000 : ℝ)|^2111 ≤ (2567996959/4000000000000 : ℝ)^1599
        have hw : |(-38179669/10000000000 : ℝ)|=(38179669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5912456931/10000000000 : ℝ)|^2111 ≤ (49967551880947/100000000000000 : ℝ)^1599
        have hw : |(5912456931/10000000000 : ℝ)|=(5912456931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956259669/5000000000 : ℝ)|^2111 ≤ (49968248176933/100000000000000 : ℝ)^1599
        have hw : |(2956259669/5000000000 : ℝ)|=(2956259669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2297/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2293/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7067/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2293/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2293/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7067/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2293/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2293/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7067/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2293/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2293/20000 : ℝ) ^ (8443/2048 : ℝ) ≤ (6624978116136153/50000000000000000000 : ℝ) := by
    have hpowers : (2293/20000 : ℝ)^8443 ≤ (6624978116136153/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2293 : ℕ)^8443*50000000000000000000^2048 ≤ 6624978116136153^2048*20000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2293 20000 6624978116136153 50000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2293/20000 : ℝ)) (X := (6624978116136153/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7067/50000 : ℝ) ^ (8443/2048 : ℝ) ≤ (31399160149354153/100000000000000000000 : ℝ) := by
    have hpowers : (7067/50000 : ℝ)^8443 ≤ (31399160149354153/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7067 : ℕ)^8443*100000000000000000000^2048 ≤ 31399160149354153^2048*50000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7067 50000 31399160149354153 100000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7067/50000 : ℝ)) (X := (31399160149354153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006624978116136153/25000000000000000000 : ℝ) ≤ (10000642738065659/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (25006624978116136153/25000000000000000000 : ℝ)^2048 ≤ (10000642738065659/10000000000000000 : ℝ)^8443 := by
      have hnat : (25006624978116136153 : ℕ)^2048*10000000000000000^8443 ≤ 10000642738065659^8443*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006624978116136153 25000000000000000000 10000642738065659 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000642738065659/10000000000000000 : ℝ)) (X := (25006624978116136153/25000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044649116381626459/100000000000000000000 : ℝ) ≤ (125013535759247/125000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (100044649116381626459/100000000000000000000 : ℝ)^2048 ≤ (125013535759247/125000000000000 : ℝ)^8443 := by
      have hnat : (100044649116381626459 : ℕ)^2048*125000000000000^8443 ≤ 125013535759247^8443*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044649116381626459 100000000000000000000 125013535759247 125000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125013535759247/125000000000000 : ℝ)) (X := (100044649116381626459/100000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031399160149354153/50000000000000000000 : ℝ) ≤ (10001522983413861/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50031399160149354153/50000000000000000000 : ℝ)^2048 ≤ (10001522983413861/10000000000000000 : ℝ)^8443 := by
      have hnat : (50031399160149354153 : ℕ)^2048*10000000000000000^8443 ≤ 10001522983413861^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031399160149354153 50000000000000000000 10001522983413861 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001522983413861/10000000000000000 : ℝ)) (X := (50031399160149354153/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6624978116136153/50000000000000000000 : ℝ) ≤ ((26681623454980107941/26690000000000000000 : ℝ)+2*(440122674101/266900000000000 : ℝ)*(2293/20000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (26681623454980107941/26690000000000000000 : ℝ)+2*(440122674101/266900000000000 : ℝ)*(2293/20000 : ℝ)=(10000642738065659/10000000000000000 : ℝ) by norm_num, show 1+2*(6624978116136153/50000000000000000000 : ℝ)=(25006624978116136153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31399160149354153/100000000000000000000 : ℝ)+(6624978116136153/50000000000000000000 : ℝ) ≤ ((26681623454980107941/26690000000000000000 : ℝ)+(440122674101/266900000000000 : ℝ)*((7067/50000 : ℝ)+(2293/20000 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (26681623454980107941/26690000000000000000 : ℝ)+(440122674101/266900000000000 : ℝ)*((7067/50000 : ℝ)+(2293/20000 : ℝ))=(125013535759247/125000000000000 : ℝ) by norm_num, show 1+(31399160149354153/100000000000000000000 : ℝ)+(6624978116136153/50000000000000000000 : ℝ)=(100044649116381626459/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31399160149354153/100000000000000000000 : ℝ) ≤ ((26681623454980107941/26690000000000000000 : ℝ)+2*(440122674101/266900000000000 : ℝ)*(7067/50000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (26681623454980107941/26690000000000000000 : ℝ)+2*(440122674101/266900000000000 : ℝ)*(7067/50000 : ℝ)=(10001522983413861/10000000000000000 : ℝ) by norm_num, show 1+2*(31399160149354153/100000000000000000000 : ℝ)=(50031399160149354153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26681623454980107941/26690000000000000000 : ℝ)*(X 1 0+X 2 0)+(440122674101/266900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (7067/50000 : ℝ)) (c := (26681623454980107941/26690000000000000000 : ℝ)) (alpha := (440122674101/266900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26681623454980107941/26690000000000000000 : ℝ)*(X 0 1+X 2 1)+(440122674101/266900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (7067/50000 : ℝ)) (c := (26681623454980107941/26690000000000000000 : ℝ)) (alpha := (440122674101/266900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26681623454980107941/26690000000000000000 : ℝ)*(X 0 2+X 1 2)+(440122674101/266900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (7067/50000 : ℝ)) (c := (26681623454980107941/26690000000000000000 : ℝ)) (alpha := (440122674101/266900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2115810717/10000000000 : ℝ)*X 0 0+(13478037/25000000 : ℝ)*X 0 1+(2633579089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344307581/10000000000 : ℝ)*X 1 0+(-1089355443/5000000000 : ℝ)*X 1 1+(1053431663/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344307397/10000000000 : ℝ)*X 2 0+(1316789579/2500000000 : ℝ)*X 2 1+(-544677783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349530823/10000000000 : ℝ)*X 0 0+(264078503/625000000 : ℝ)*X 0 1+(2238675363/5000000000 : ℝ)*X 0 2+(4349530823/10000000000 : ℝ)*X 1 0+(264078503/625000000 : ℝ)*X 1 1+(2238675363/5000000000 : ℝ)*X 1 2+(4349530823/10000000000 : ℝ)*X 2 0+(264078503/625000000 : ℝ)*X 2 1+(2238675363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528953943/2500000000 : ℝ)*X 0 0+(526747167/1000000000 : ℝ)*X 0 1+(1347724971/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656317649/5000000000 : ℝ)*X 1 0+(-2054969359/10000000000 : ℝ)*X 1 1+(2695449687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656317761/5000000000 : ℝ)*X 2 0+(5390899003/10000000000 : ℝ)*X 2 1+(-51374239/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174770323/5000000000 : ℝ)*X 0 0+(447671283/1000000000 : ℝ)*X 0 1+(2112947973/5000000000 : ℝ)*X 0 2+(2174770323/5000000000 : ℝ)*X 1 0+(447671283/1000000000 : ℝ)*X 1 1+(2112947973/5000000000 : ℝ)*X 1 2+(2174770323/5000000000 : ℝ)*X 2 0+(447671283/1000000000 : ℝ)*X 2 1+(2112947973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-38179669/10000000000 : ℝ)*X 0 0+(5912456931/10000000000 : ℝ)*X 0 1+(2956259669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (897360573960860182856010957/66725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211443657/50000000000000 : ℝ)*(lower2) + (191030011/100000000000000 : ℝ)*(lower3) + (594308409/100000000000000 : ℝ)*(lower4) + (232404089/100000000000000 : ℝ)*(lower5) + (601380879085141/10000000000000 : ℝ)*(major0) + (601380879085141/10000000000000 : ℝ)*(major1) + (601380879085141/10000000000000 : ℝ)*(major2) + (8060845995551711/100000000000000 : ℝ)*(sp0) + (40304249283311/500000000000 : ℝ)*(sp1) + (8060842562653797/100000000000000 : ℝ)*(sp2) + (991691568610209/25000000000000 : ℝ)*(sp3) + (62644483/6250000000000 : ℝ)*(sp5) + (8296320129/100000000000000 : ℝ)*(sp6) + (972684443/20000000000000 : ℝ)*(sp8) + (991691568610209/25000000000000 : ℝ)*(f.failure) + (4030425429486963/50000000000000 : ℝ)*(f.sum) + (31888202385783/667250000000000000000000000 : ℝ)*base66 + (2303558085111604681/266900000000000000000000000000000 : ℝ)*base67 + (349006128361704681/266900000000000000000000000000000 : ℝ)*base69 + (6412296307973495319/266900000000000000000000000000000 : ℝ)*base72 + (5989026386569/1334500000000000000000000000 : ℝ)*base73 + (177545553118104681/266900000000000000000000000000000 : ℝ)*base75 + (28851080010585804681/266900000000000000000000000000000 : ℝ)*base77 + (2856624989181004681/266900000000000000000000000000000 : ℝ)*base79 + (2093080495833/1334500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (806519/1250000000000000000000 : ℝ)*base90 + (806519/1250000000000000000000 : ℝ)*base92 + (806519/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1155660805758420836102937/785000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44753039/6250000000000 : ℝ)*(lower2) + (174605641/100000000000000 : ℝ)*(lower3) + (534564577/100000000000000 : ℝ)*(lower4) + (337274771/50000000000000 : ℝ)*(lower5) + (60444828118659/1000000000000 : ℝ)*(major0) + (60444828118659/1000000000000 : ℝ)*(major1) + (60444828118659/1000000000000 : ℝ)*(major2) + (49875353769/100000000000000 : ℝ)*(sp0) + (6628407243/100000000000000 : ℝ)*(sp3) + (1620381857434163/20000000000000 : ℝ)*(sp4) + (50637290125893/625000000000 : ℝ)*(sp5) + (50637290125893/625000000000 : ℝ)*(sp6) + (1993496263054503/50000000000000 : ℝ)*(sp7) + (1451523659/20000000000000 : ℝ)*(sp8) + (3189599323613/80000000000 : ℝ)*(f.failure) + (50637290125893/625000000000 : ℝ)*(f.sum) + (5324324182709/157000000000000000000000000 : ℝ)*base66 + (50687424706833007/1570000000000000000000000000000 : ℝ)*base67 + (56944035463843007/1570000000000000000000000000000 : ℝ)*base69 + (36354989588213007/1570000000000000000000000000000 : ℝ)*base71 + (75029247109/19625000000000000000000000 : ℝ)*base73 + (38937218657083007/1570000000000000000000000000000 : ℝ)*base75 + (23619141549813007/1570000000000000000000000000000 : ℝ)*base77 + (46051993827183007/1570000000000000000000000000000 : ℝ)*base79 + (331597327691/78500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (16283/4000000000000000000 : ℝ)*base90 + (16283/4000000000000000000 : ℝ)*base92 + (16283/4000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1251_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1251_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1251_s7_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-423165423/2000000000 : ℝ)*x 0 + (1347756241/2500000000 : ℝ)*x 1 + (1316834297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423165423/2000000000 : ℝ)^2111 ≤ (321690959373/2500000000000 : ℝ)^1599 := by
    have hnat : (423165423 : ℕ)^2111*2500000000000^1599 ≤ 321690959373^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423165423 2000000000 321690959373 2500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347756241/2500000000 : ℝ)^2111 ≤ (44233619046091/100000000000000 : ℝ)^1599 := by
    have hnat : (1347756241 : ℕ)^2111*100000000000000^1599 ≤ 44233619046091^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347756241 2500000000 44233619046091 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316834297/2500000000 : ℝ)^2111 ≤ (428987425727/1000000000000 : ℝ)^1599 := by
    have hnat : (1316834297 : ℕ)^2111*1000000000000^1599 ≤ 428987425727^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316834297 2500000000 428987425727 1000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423165423/2000000000 : ℝ), (1347756241/2500000000 : ℝ), (1316834297/2500000000 : ℝ)] ![(321690959373/2500000000000 : ℝ), (44233619046091/100000000000000 : ℝ), (428987425727/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423165423/2000000000 : ℝ)|^2111 ≤ (321690959373/2500000000000 : ℝ)^1599
        have hw : |(-423165423/2000000000 : ℝ)|=(423165423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347756241/2500000000 : ℝ)|^2111 ≤ (44233619046091/100000000000000 : ℝ)^1599
        have hw : |(1347756241/2500000000 : ℝ)|=(1347756241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316834297/2500000000 : ℝ)|^2111 ≤ (428987425727/1000000000000 : ℝ)^1599
        have hw : |(1316834297/2500000000 : ℝ)|=(1316834297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344257787/10000000000 : ℝ)*x 0 + (-1089267561/5000000000 : ℝ)*x 1 + (5267340827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344257787/10000000000 : ℝ)^2111 ≤ (349821821451/800000000000 : ℝ)^1599 := by
    have hnat : (5344257787 : ℕ)^2111*800000000000^1599 ≤ 349821821451^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344257787 10000000000 349821821451 800000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089267561/5000000000 : ℝ)^2111 ≤ (13373490612707/100000000000000 : ℝ)^1599 := by
    have hnat : (1089267561 : ℕ)^2111*100000000000000^1599 ≤ 13373490612707^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089267561 5000000000 13373490612707 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267340827/10000000000 : ℝ)^2111 ≤ (42898781699589/100000000000000 : ℝ)^1599 := by
    have hnat : (5267340827 : ℕ)^2111*100000000000000^1599 ≤ 42898781699589^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267340827 10000000000 42898781699589 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344257787/10000000000 : ℝ), (-1089267561/5000000000 : ℝ), (5267340827/10000000000 : ℝ)] ![(349821821451/800000000000 : ℝ), (13373490612707/100000000000000 : ℝ), (42898781699589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344257787/10000000000 : ℝ)|^2111 ≤ (349821821451/800000000000 : ℝ)^1599
        have hw : |(5344257787/10000000000 : ℝ)|=(5344257787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089267561/5000000000 : ℝ)|^2111 ≤ (13373490612707/100000000000000 : ℝ)^1599
        have hw : |(-1089267561/5000000000 : ℝ)|=(1089267561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267340827/10000000000 : ℝ)|^2111 ≤ (42898781699589/100000000000000 : ℝ)^1599
        have hw : |(5267340827/10000000000 : ℝ)|=(5267340827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344260657/10000000000 : ℝ)*x 0 + (5267338287/10000000000 : ℝ)*x 1 + (-435706933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344260657/10000000000 : ℝ)^2111 ≤ (21863879341741/50000000000000 : ℝ)^1599 := by
    have hnat : (5344260657 : ℕ)^2111*50000000000000^1599 ≤ 21863879341741^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344260657 10000000000 21863879341741 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267338287/10000000000 : ℝ)^2111 ≤ (5362344298657/12500000000000 : ℝ)^1599 := by
    have hnat : (5267338287 : ℕ)^2111*12500000000000^1599 ≤ 5362344298657^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267338287 10000000000 5362344298657 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435706933/2000000000 : ℝ)^2111 ≤ (3343371727251/25000000000000 : ℝ)^1599 := by
    have hnat : (435706933 : ℕ)^2111*25000000000000^1599 ≤ 3343371727251^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435706933 2000000000 3343371727251 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344260657/10000000000 : ℝ), (5267338287/10000000000 : ℝ), (-435706933/2000000000 : ℝ)] ![(21863879341741/50000000000000 : ℝ), (5362344298657/12500000000000 : ℝ), (3343371727251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344260657/10000000000 : ℝ)|^2111 ≤ (21863879341741/50000000000000 : ℝ)^1599
        have hw : |(5344260657/10000000000 : ℝ)|=(5344260657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267338287/10000000000 : ℝ)|^2111 ≤ (5362344298657/12500000000000 : ℝ)^1599
        have hw : |(5267338287/10000000000 : ℝ)|=(5267338287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435706933/2000000000 : ℝ)|^2111 ≤ (3343371727251/25000000000000 : ℝ)^1599
        have hw : |(-435706933/2000000000 : ℝ)|=(435706933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4349544733/10000000000 : ℝ)*x 0 + (4225629941/10000000000 : ℝ)*x 1 + (895393983/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349544733/10000000000 : ℝ)^2111 ≤ (33317580967259/100000000000000 : ℝ)^1599 := by
    have hnat : (4349544733 : ℕ)^2111*100000000000000^1599 ≤ 33317580967259^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349544733 10000000000 33317580967259 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225629941/10000000000 : ℝ)^2111 ≤ (3207021416431/10000000000000 : ℝ)^1599 := by
    have hnat : (4225629941 : ℕ)^2111*10000000000000^1599 ≤ 3207021416431^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225629941 10000000000 3207021416431 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895393983/2000000000 : ℝ)^2111 ≤ (6922440970821/20000000000000 : ℝ)^1599 := by
    have hnat : (895393983 : ℕ)^2111*20000000000000^1599 ≤ 6922440970821^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895393983 2000000000 6922440970821 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349544733/10000000000 : ℝ), (4225629941/10000000000 : ℝ), (895393983/2000000000 : ℝ)] ![(33317580967259/100000000000000 : ℝ), (3207021416431/10000000000000 : ℝ), (6922440970821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349544733/10000000000 : ℝ)|^2111 ≤ (33317580967259/100000000000000 : ℝ)^1599
        have hw : |(4349544733/10000000000 : ℝ)|=(4349544733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225629941/10000000000 : ℝ)|^2111 ≤ (3207021416431/10000000000000 : ℝ)^1599
        have hw : |(4225629941/10000000000 : ℝ)|=(4225629941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895393983/2000000000 : ℝ)|^2111 ≤ (6922440970821/20000000000000 : ℝ)^1599
        have hw : |(895393983/2000000000 : ℝ)|=(895393983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115831933/10000000000 : ℝ)*x 0 + (1316912717/2500000000 : ℝ)*x 1 + (5390710029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115831933/10000000000 : ℝ)^2111 ≤ (12867677058387/100000000000000 : ℝ)^1599 := by
    have hnat : (2115831933 : ℕ)^2111*100000000000000^1599 ≤ 12867677058387^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115831933 10000000000 12867677058387 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316912717/2500000000 : ℝ)^2111 ≤ (42902115322937/100000000000000 : ℝ)^1599 := by
    have hnat : (1316912717 : ℕ)^2111*100000000000000^1599 ≤ 42902115322937^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316912717 2500000000 42902115322937 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390710029/10000000000 : ℝ)^2111 ≤ (5528775950733/12500000000000 : ℝ)^1599 := by
    have hnat : (5390710029 : ℕ)^2111*12500000000000^1599 ≤ 5528775950733^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390710029 10000000000 5528775950733 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115831933/10000000000 : ℝ), (1316912717/2500000000 : ℝ), (5390710029/10000000000 : ℝ)] ![(12867677058387/100000000000000 : ℝ), (42902115322937/100000000000000 : ℝ), (5528775950733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115831933/10000000000 : ℝ)|^2111 ≤ (12867677058387/100000000000000 : ℝ)^1599
        have hw : |(-2115831933/10000000000 : ℝ)|=(2115831933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316912717/2500000000 : ℝ)|^2111 ≤ (42902115322937/100000000000000 : ℝ)^1599
        have hw : |(1316912717/2500000000 : ℝ)|=(1316912717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390710029/10000000000 : ℝ)|^2111 ≤ (5528775950733/12500000000000 : ℝ)^1599
        have hw : |(5390710029/10000000000 : ℝ)|=(5390710029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656340561/5000000000 : ℝ)*x 0 + (-256895637/1250000000 : ℝ)*x 1 + (5390710029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656340561/5000000000 : ℝ)^2111 ≤ (43386955628169/100000000000000 : ℝ)^1599 := by
    have hnat : (2656340561 : ℕ)^2111*100000000000000^1599 ≤ 43386955628169^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656340561 5000000000 43386955628169 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256895637/1250000000 : ℝ)^2111 ≤ (2476567352229/20000000000000 : ℝ)^1599 := by
    have hnat : (256895637 : ℕ)^2111*20000000000000^1599 ≤ 2476567352229^1599*1250000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256895637 1250000000 2476567352229 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390710029/10000000000 : ℝ)^2111 ≤ (5528775950733/12500000000000 : ℝ)^1599 := by
    have hnat : (5390710029 : ℕ)^2111*12500000000000^1599 ≤ 5528775950733^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390710029 10000000000 5528775950733 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656340561/5000000000 : ℝ), (-256895637/1250000000 : ℝ), (5390710029/10000000000 : ℝ)] ![(43386955628169/100000000000000 : ℝ), (2476567352229/20000000000000 : ℝ), (5528775950733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656340561/5000000000 : ℝ)|^2111 ≤ (43386955628169/100000000000000 : ℝ)^1599
        have hw : |(2656340561/5000000000 : ℝ)|=(2656340561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256895637/1250000000 : ℝ)|^2111 ≤ (2476567352229/20000000000000 : ℝ)^1599
        have hw : |(-256895637/1250000000 : ℝ)|=(256895637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390710029/10000000000 : ℝ)|^2111 ≤ (5528775950733/12500000000000 : ℝ)^1599
        have hw : |(5390710029/10000000000 : ℝ)|=(5390710029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_6 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312681123/10000000000 : ℝ)*x 0 + (5390710029/10000000000 : ℝ)*x 1 + (-2055165093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312681123/10000000000 : ℝ)^2111 ≤ (867739112779/2000000000000 : ℝ)^1599 := by
    have hnat : (5312681123 : ℕ)^2111*2000000000000^1599 ≤ 867739112779^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312681123 10000000000 867739112779 2000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390710029/10000000000 : ℝ)^2111 ≤ (5528775950733/12500000000000 : ℝ)^1599 := by
    have hnat : (5390710029 : ℕ)^2111*12500000000000^1599 ≤ 5528775950733^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390710029 10000000000 5528775950733 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055165093/10000000000 : ℝ)^2111 ≤ (12382836737281/100000000000000 : ℝ)^1599 := by
    have hnat : (2055165093 : ℕ)^2111*100000000000000^1599 ≤ 12382836737281^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055165093 10000000000 12382836737281 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312681123/10000000000 : ℝ), (5390710029/10000000000 : ℝ), (-2055165093/10000000000 : ℝ)] ![(867739112779/2000000000000 : ℝ), (5528775950733/12500000000000 : ℝ), (12382836737281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312681123/10000000000 : ℝ)|^2111 ≤ (867739112779/2000000000000 : ℝ)^1599
        have hw : |(5312681123/10000000000 : ℝ)|=(5312681123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390710029/10000000000 : ℝ)|^2111 ≤ (5528775950733/12500000000000 : ℝ)^1599
        have hw : |(5390710029/10000000000 : ℝ)|=(5390710029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055165093/10000000000 : ℝ)|^2111 ≤ (12382836737281/100000000000000 : ℝ)^1599
        have hw : |(-2055165093/10000000000 : ℝ)|=(2055165093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_7 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (869909999/2000000000 : ℝ)*x 0 + (4476337203/10000000000 : ℝ)*x 1 + (4226269127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869909999/2000000000 : ℝ)^2111 ≤ (1665881709029/5000000000000 : ℝ)^1599 := by
    have hnat : (869909999 : ℕ)^2111*5000000000000^1599 ≤ 1665881709029^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869909999 2000000000 1665881709029 5000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476337203/10000000000 : ℝ)^2111 ≤ (34605747105957/100000000000000 : ℝ)^1599 := by
    have hnat : (4476337203 : ℕ)^2111*100000000000000^1599 ≤ 34605747105957^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476337203 10000000000 34605747105957 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226269127/10000000000 : ℝ)^2111 ≤ (32076618704271/100000000000000 : ℝ)^1599 := by
    have hnat : (4226269127 : ℕ)^2111*100000000000000^1599 ≤ 32076618704271^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226269127 10000000000 32076618704271 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869909999/2000000000 : ℝ), (4476337203/10000000000 : ℝ), (4226269127/10000000000 : ℝ)] ![(1665881709029/5000000000000 : ℝ), (34605747105957/100000000000000 : ℝ), (32076618704271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869909999/2000000000 : ℝ)|^2111 ≤ (1665881709029/5000000000000 : ℝ)^1599
        have hw : |(869909999/2000000000 : ℝ)|=(869909999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476337203/10000000000 : ℝ)|^2111 ≤ (34605747105957/100000000000000 : ℝ)^1599
        have hw : |(4476337203/10000000000 : ℝ)|=(4476337203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226269127/10000000000 : ℝ)|^2111 ≤ (32076618704271/100000000000000 : ℝ)^1599
        have hw : |(4226269127/10000000000 : ℝ)|=(4226269127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s7_8 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-31019229/5000000000 : ℝ)*x 0 + (2954946891/5000000000 : ℝ)*x 1 + (5909913979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31019229/5000000000 : ℝ)^2111 ≤ (15232836549/12500000000000 : ℝ)^1599 := by
    have hnat : (31019229 : ℕ)^2111*12500000000000^1599 ≤ 15232836549^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31019229 5000000000 15232836549 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2954946891/5000000000 : ℝ)^2111 ≤ (6242369499361/12500000000000 : ℝ)^1599 := by
    have hnat : (2954946891 : ℕ)^2111*12500000000000^1599 ≤ 6242369499361^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2954946891 5000000000 6242369499361 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5909913979/10000000000 : ℝ)^2111 ≤ (49939181308099/100000000000000 : ℝ)^1599 := by
    have hnat : (5909913979 : ℕ)^2111*100000000000000^1599 ≤ 49939181308099^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5909913979 10000000000 49939181308099 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31019229/5000000000 : ℝ), (2954946891/5000000000 : ℝ), (5909913979/10000000000 : ℝ)] ![(15232836549/12500000000000 : ℝ), (6242369499361/12500000000000 : ℝ), (49939181308099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31019229/5000000000 : ℝ)|^2111 ≤ (15232836549/12500000000000 : ℝ)^1599
        have hw : |(-31019229/5000000000 : ℝ)|=(31019229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2954946891/5000000000 : ℝ)|^2111 ≤ (6242369499361/12500000000000 : ℝ)^1599
        have hw : |(2954946891/5000000000 : ℝ)|=(2954946891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5909913979/10000000000 : ℝ)|^2111 ≤ (49939181308099/100000000000000 : ℝ)^1599
        have hw : |(5909913979/10000000000 : ℝ)|=(5909913979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11489/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2297/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2297/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2297/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2297/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2297/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2297/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2297/20000 : ℝ) ^ (8443/2048 : ℝ) ≤ (13345503856310293/100000000000000000000 : ℝ) := by
    have hpowers : (2297/20000 : ℝ)^8443 ≤ (13345503856310293/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2297 : ℕ)^8443*100000000000000000000^2048 ≤ 13345503856310293^2048*20000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2297 20000 13345503856310293 100000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2297/20000 : ℝ)) (X := (13345503856310293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14113/100000 : ℝ) ^ (8443/2048 : ℝ) ≤ (24380686989239/78125000000000000 : ℝ) := by
    have hpowers : (14113/100000 : ℝ)^8443 ≤ (24380686989239/78125000000000000 : ℝ)^2048 := by
      have hnat : (14113 : ℕ)^8443*78125000000000000^2048 ≤ 24380686989239^2048*100000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14113 100000 24380686989239 78125000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14113/100000 : ℝ)) (X := (24380686989239/78125000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013345503856310293/50000000000000000000 : ℝ) ≤ (10000647372487657/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50013345503856310293/50000000000000000000 : ℝ)^2048 ≤ (10000647372487657/10000000000000000 : ℝ)^8443 := by
      have hnat : (50013345503856310293 : ℕ)^2048*10000000000000000^8443 ≤ 10000647372487657^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013345503856310293 50000000000000000000 10000647372487657 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000647372487657/10000000000000000 : ℝ)) (X := (50013345503856310293/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044552783202536213/100000000000000000000 : ℝ) ≤ (2500270131199011/2500000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (100044552783202536213/100000000000000000000 : ℝ)^2048 ≤ (2500270131199011/2500000000000000 : ℝ)^8443 := by
      have hnat : (100044552783202536213 : ℕ)^2048*2500000000000000^8443 ≤ 2500270131199011^8443*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044552783202536213 100000000000000000000 2500270131199011 2500000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500270131199011/2500000000000000 : ℝ)) (X := (100044552783202536213/100000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (39086880686989239/39062500000000000 : ℝ) ≤ (10001513677104431/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (39086880686989239/39062500000000000 : ℝ)^2048 ≤ (10001513677104431/10000000000000000 : ℝ)^8443 := by
      have hnat : (39086880686989239 : ℕ)^2048*10000000000000000^8443 ≤ 10001513677104431^8443*39062500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39086880686989239 39062500000000000 10001513677104431 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001513677104431/10000000000000000 : ℝ)) (X := (39086880686989239/39062500000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13345503856310293/100000000000000000000 : ℝ) ≤ ((13135875893186956603/13140000000000000000 : ℝ)+2*(433152308387/262800000000000 : ℝ)*(2297/20000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (13135875893186956603/13140000000000000000 : ℝ)+2*(433152308387/262800000000000 : ℝ)*(2297/20000 : ℝ)=(10000647372487657/10000000000000000 : ℝ) by norm_num, show 1+2*(13345503856310293/100000000000000000000 : ℝ)=(50013345503856310293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24380686989239/78125000000000000 : ℝ)+(13345503856310293/100000000000000000000 : ℝ) ≤ ((13135875893186956603/13140000000000000000 : ℝ)+(433152308387/262800000000000 : ℝ)*((14113/100000 : ℝ)+(2297/20000 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (13135875893186956603/13140000000000000000 : ℝ)+(433152308387/262800000000000 : ℝ)*((14113/100000 : ℝ)+(2297/20000 : ℝ))=(2500270131199011/2500000000000000 : ℝ) by norm_num, show 1+(24380686989239/78125000000000000 : ℝ)+(13345503856310293/100000000000000000000 : ℝ)=(100044552783202536213/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24380686989239/78125000000000000 : ℝ) ≤ ((13135875893186956603/13140000000000000000 : ℝ)+2*(433152308387/262800000000000 : ℝ)*(14113/100000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (13135875893186956603/13140000000000000000 : ℝ)+2*(433152308387/262800000000000 : ℝ)*(14113/100000 : ℝ)=(10001513677104431/10000000000000000 : ℝ) by norm_num, show 1+2*(24380686989239/78125000000000000 : ℝ)=(39086880686989239/39062500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13135875893186956603/13140000000000000000 : ℝ)*(X 1 0+X 2 0)+(433152308387/262800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (2297/20000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (13135875893186956603/13140000000000000000 : ℝ)) (alpha := (433152308387/262800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13135875893186956603/13140000000000000000 : ℝ)*(X 0 1+X 2 1)+(433152308387/262800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (2297/20000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (13135875893186956603/13140000000000000000 : ℝ)) (alpha := (433152308387/262800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13135875893186956603/13140000000000000000 : ℝ)*(X 0 2+X 1 2)+(433152308387/262800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (2297/20000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (13135875893186956603/13140000000000000000 : ℝ)) (alpha := (433152308387/262800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423165423/2000000000 : ℝ)*X 0 0+(1347756241/2500000000 : ℝ)*X 0 1+(1316834297/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344257787/10000000000 : ℝ)*X 1 0+(-1089267561/5000000000 : ℝ)*X 1 1+(5267340827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344260657/10000000000 : ℝ)*X 2 0+(5267338287/10000000000 : ℝ)*X 2 1+(-435706933/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349544733/10000000000 : ℝ)*X 0 0+(4225629941/10000000000 : ℝ)*X 0 1+(895393983/2000000000 : ℝ)*X 0 2+(4349544733/10000000000 : ℝ)*X 1 0+(4225629941/10000000000 : ℝ)*X 1 1+(895393983/2000000000 : ℝ)*X 1 2+(4349544733/10000000000 : ℝ)*X 2 0+(4225629941/10000000000 : ℝ)*X 2 1+(895393983/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115831933/10000000000 : ℝ)*X 0 0+(1316912717/2500000000 : ℝ)*X 0 1+(5390710029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656340561/5000000000 : ℝ)*X 1 0+(-256895637/1250000000 : ℝ)*X 1 1+(5390710029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312681123/10000000000 : ℝ)*X 2 0+(5390710029/10000000000 : ℝ)*X 2 1+(-2055165093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869909999/2000000000 : ℝ)*X 0 0+(4476337203/10000000000 : ℝ)*X 0 1+(4226269127/10000000000 : ℝ)*X 0 2+(869909999/2000000000 : ℝ)*X 1 0+(4476337203/10000000000 : ℝ)*X 1 1+(4226269127/10000000000 : ℝ)*X 1 2+(869909999/2000000000 : ℝ)*X 2 0+(4476337203/10000000000 : ℝ)*X 2 1+(4226269127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-31019229/5000000000 : ℝ)*X 0 0+(2954946891/5000000000 : ℝ)*X 0 1+(5909913979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29275649116261016832221/4380000000000000000000000000 : ℝ) := by norm_num
    linear_combination (921350659/25000000000000 : ℝ)*(lower2) + (1463924889/100000000000000 : ℝ)*(lower4) + (740942313/100000000000000 : ℝ)*(lower5) + (6031917051337577/100000000000000 : ℝ)*(major0) + (6031917051337577/100000000000000 : ℝ)*(major1) + (6031917051337577/100000000000000 : ℝ)*(major2) + (2021238100703933/25000000000000 : ℝ)*(sp0) + (8085123222187167/100000000000000 : ℝ)*(sp1) + (808509188777679/10000000000000 : ℝ)*(sp2) + (994665696478147/25000000000000 : ℝ)*(sp3) + (30948454893/20000000000000 : ℝ)*(sp4) + (15667205189/50000000000000 : ℝ)*(sp6) + (11967944361/25000000000000 : ℝ)*(sp7) + (1607709697/10000000000000 : ℝ)*(sp8) + (3978710657690033/100000000000000 : ℝ)*(f.failure) + (8085123222187167/100000000000000 : ℝ)*(f.sum) + (7306319301439/13140000000000000000000000000 : ℝ)*base65 + (15670320830954879069/1314000000000000000000000000000000 : ℝ)*base68 + (6198384212271120931/1314000000000000000000000000000000 : ℝ)*base69 + (124736065165035120931/1314000000000000000000000000000000 : ℝ)*base71 + (40387827888941/13140000000000000000000000000 : ℝ)*base74 + (3029183907579120931/1314000000000000000000000000000000 : ℝ)*base75 + (13390860723794879069/1314000000000000000000000000000000 : ℝ)*base78 + (156947598530879069/1314000000000000000000000000000000 : ℝ)*base80 + (26887213479739/13140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26689497/5000000000000000000000 : ℝ)*base89 + (26689497/5000000000000000000000 : ℝ)*base91 + (26689497/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143496380543622419523283287/36500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101183251/50000000000000 : ℝ)*(lower2) + (66977747/100000000000000 : ℝ)*(lower3) + (40310777/20000000000000 : ℝ)*(lower4) + (32059069/50000000000000 : ℝ)*(lower5) + (3031273516760629/50000000000000 : ℝ)*(major0) + (3031273516760629/50000000000000 : ℝ)*(major1) + (3031273516760629/50000000000000 : ℝ)*(major2) + (2310012377/100000000000000 : ℝ)*(sp0) + (1708493349/100000000000000 : ℝ)*(sp3) + (325047011909739/4000000000000 : ℝ)*(sp4) + (8126179446667641/100000000000000 : ℝ)*(sp5) + (8126179446667641/100000000000000 : ℝ)*(sp6) + (799782556166919/20000000000000 : ℝ)*(sp7) + (1838911789/100000000000000 : ℝ)*(sp8) + (499864311165993/12500000000000 : ℝ)*(f.failure) + (8126179446667641/100000000000000 : ℝ)*(f.sum) + (29755804166077/6570000000000000000000000000 : ℝ)*base66 + (8344850748906866713/657000000000000000000000000000000 : ℝ)*base68 + (8209815608640866713/657000000000000000000000000000000 : ℝ)*base70 + (3350776363374866713/657000000000000000000000000000000 : ℝ)*base72 + (24607911597637/6570000000000000000000000000 : ℝ)*base74 + (5020268843739866713/657000000000000000000000000000000 : ℝ)*base76 + (9557237003511866713/657000000000000000000000000000000 : ℝ)*base78 + (1400235828897866713/657000000000000000000000000000000 : ℝ)*base80 + (60157830950167/6570000000000000000000000000 : ℝ)*base82 + (5777137/625000000000000000000 : ℝ)*base89 + (5777137/625000000000000000000 : ℝ)*base91 + (5777137/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1251_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1251_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1251_s8_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-528957473/2500000000 : ℝ)*x 0 + (5390986327/10000000000 : ℝ)*x 1 + (5267374039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528957473/2500000000 : ℝ)^2111 ≤ (6433830335651/50000000000000 : ℝ)^1599 := by
    have hnat : (528957473 : ℕ)^2111*50000000000000^1599 ≤ 6433830335651^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528957473 2500000000 6433830335651 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390986327/10000000000 : ℝ)^2111 ≤ (345571879053/781250000000 : ℝ)^1599 := by
    have hnat : (5390986327 : ℕ)^2111*781250000000^1599 ≤ 345571879053^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390986327 10000000000 345571879053 781250000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267374039/10000000000 : ℝ)^2111 ≤ (8579827759741/20000000000000 : ℝ)^1599 := by
    have hnat : (5267374039 : ℕ)^2111*20000000000000^1599 ≤ 8579827759741^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267374039 10000000000 8579827759741 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528957473/2500000000 : ℝ), (5390986327/10000000000 : ℝ), (5267374039/10000000000 : ℝ)] ![(6433830335651/50000000000000 : ℝ), (345571879053/781250000000 : ℝ), (8579827759741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528957473/2500000000 : ℝ)|^2111 ≤ (6433830335651/50000000000000 : ℝ)^1599
        have hw : |(-528957473/2500000000 : ℝ)|=(528957473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390986327/10000000000 : ℝ)|^2111 ≤ (345571879053/781250000000 : ℝ)^1599
        have hw : |(5390986327/10000000000 : ℝ)|=(5390986327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267374039/10000000000 : ℝ)|^2111 ≤ (8579827759741/20000000000000 : ℝ)^1599
        have hw : |(5267374039/10000000000 : ℝ)|=(5267374039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s8_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344249717/10000000000 : ℝ)*x 0 + (-2178501883/10000000000 : ℝ)*x 1 + (5267373987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344249717/10000000000 : ℝ)^2111 ≤ (43727640508231/100000000000000 : ℝ)^1599 := by
    have hnat : (5344249717 : ℕ)^2111*100000000000000^1599 ≤ 43727640508231^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344249717 10000000000 43727640508231 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178501883/10000000000 : ℝ)^2111 ≤ (13373221231763/100000000000000 : ℝ)^1599 := by
    have hnat : (2178501883 : ℕ)^2111*100000000000000^1599 ≤ 13373221231763^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178501883 10000000000 13373221231763 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267373987/10000000000 : ℝ)^2111 ≤ (21449569119797/50000000000000 : ℝ)^1599 := by
    have hnat : (5267373987 : ℕ)^2111*50000000000000^1599 ≤ 21449569119797^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267373987 10000000000 21449569119797 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344249717/10000000000 : ℝ), (-2178501883/10000000000 : ℝ), (5267373987/10000000000 : ℝ)] ![(43727640508231/100000000000000 : ℝ), (13373221231763/100000000000000 : ℝ), (21449569119797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344249717/10000000000 : ℝ)|^2111 ≤ (43727640508231/100000000000000 : ℝ)^1599
        have hw : |(5344249717/10000000000 : ℝ)|=(5344249717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178501883/10000000000 : ℝ)|^2111 ≤ (13373221231763/100000000000000 : ℝ)^1599
        have hw : |(-2178501883/10000000000 : ℝ)|=(2178501883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267373987/10000000000 : ℝ)|^2111 ≤ (21449569119797/50000000000000 : ℝ)^1599
        have hw : |(5267373987/10000000000 : ℝ)|=(5267373987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s8_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068849937/2000000000 : ℝ)*x 0 + (5267374023/10000000000 : ℝ)*x 1 + (-1089250939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068849937/2000000000 : ℝ)^2111 ≤ (43727640162563/100000000000000 : ℝ)^1599 := by
    have hnat : (1068849937 : ℕ)^2111*100000000000000^1599 ≤ 43727640162563^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068849937 2000000000 43727640162563 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267374023/10000000000 : ℝ)^2111 ≤ (42899138626671/100000000000000 : ℝ)^1599 := by
    have hnat : (5267374023 : ℕ)^2111*100000000000000^1599 ≤ 42899138626671^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267374023 10000000000 42899138626671 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089250939/5000000000 : ℝ)^2111 ≤ (6686610595621/50000000000000 : ℝ)^1599 := by
    have hnat : (1089250939 : ℕ)^2111*50000000000000^1599 ≤ 6686610595621^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089250939 5000000000 6686610595621 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068849937/2000000000 : ℝ), (5267374023/10000000000 : ℝ), (-1089250939/5000000000 : ℝ)] ![(43727640162563/100000000000000 : ℝ), (42899138626671/100000000000000 : ℝ), (6686610595621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068849937/2000000000 : ℝ)|^2111 ≤ (43727640162563/100000000000000 : ℝ)^1599
        have hw : |(1068849937/2000000000 : ℝ)|=(1068849937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267374023/10000000000 : ℝ)|^2111 ≤ (42899138626671/100000000000000 : ℝ)^1599
        have hw : |(5267374023/10000000000 : ℝ)|=(5267374023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089250939/5000000000 : ℝ)|^2111 ≤ (6686610595621/50000000000000 : ℝ)^1599
        have hw : |(-1089250939/5000000000 : ℝ)|=(1089250939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s8_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4349542367/10000000000 : ℝ)*x 0 + (1056426427/2500000000 : ℝ)*x 1 + (4476897881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349542367/10000000000 : ℝ)^2111 ≤ (16658778520243/50000000000000 : ℝ)^1599 := by
    have hnat : (4349542367 : ℕ)^2111*50000000000000^1599 ≤ 16658778520243^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349542367 10000000000 16658778520243 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056426427/2500000000 : ℝ)^2111 ≤ (16035486660573/50000000000000 : ℝ)^1599 := by
    have hnat : (1056426427 : ℕ)^2111*50000000000000^1599 ≤ 16035486660573^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056426427 2500000000 16035486660573 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476897881/10000000000 : ℝ)^2111 ≤ (17305734813701/50000000000000 : ℝ)^1599 := by
    have hnat : (4476897881 : ℕ)^2111*50000000000000^1599 ≤ 17305734813701^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476897881 10000000000 17305734813701 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349542367/10000000000 : ℝ), (1056426427/2500000000 : ℝ), (4476897881/10000000000 : ℝ)] ![(16658778520243/50000000000000 : ℝ), (16035486660573/50000000000000 : ℝ), (17305734813701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349542367/10000000000 : ℝ)|^2111 ≤ (16658778520243/50000000000000 : ℝ)^1599
        have hw : |(4349542367/10000000000 : ℝ)|=(4349542367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056426427/2500000000 : ℝ)|^2111 ≤ (16035486660573/50000000000000 : ℝ)^1599
        have hw : |(1056426427/2500000000 : ℝ)|=(1056426427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476897881/10000000000 : ℝ)|^2111 ≤ (17305734813701/50000000000000 : ℝ)^1599
        have hw : |(4476897881/10000000000 : ℝ)|=(4476897881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s8_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-423166873/2000000000 : ℝ)*x 0 + (1316921437/2500000000 : ℝ)*x 1 + (5390673603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423166873/2000000000 : ℝ)^2111 ≤ (12867696584797/100000000000000 : ℝ)^1599 := by
    have hnat : (423166873 : ℕ)^2111*100000000000000^1599 ≤ 12867696584797^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423166873 2000000000 12867696584797 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316921437/2500000000 : ℝ)^2111 ≤ (42902490363661/100000000000000 : ℝ)^1599 := by
    have hnat : (1316921437 : ℕ)^2111*100000000000000^1599 ≤ 42902490363661^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316921437 2500000000 42902490363661 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390673603/10000000000 : ℝ)^2111 ≤ (2764363314757/6250000000000 : ℝ)^1599 := by
    have hnat : (5390673603 : ℕ)^2111*6250000000000^1599 ≤ 2764363314757^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390673603 10000000000 2764363314757 6250000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423166873/2000000000 : ℝ), (1316921437/2500000000 : ℝ), (5390673603/10000000000 : ℝ)] ![(12867696584797/100000000000000 : ℝ), (42902490363661/100000000000000 : ℝ), (2764363314757/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423166873/2000000000 : ℝ)|^2111 ≤ (12867696584797/100000000000000 : ℝ)^1599
        have hw : |(-423166873/2000000000 : ℝ)|=(423166873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316921437/2500000000 : ℝ)|^2111 ≤ (42902490363661/100000000000000 : ℝ)^1599
        have hw : |(1316921437/2500000000 : ℝ)|=(1316921437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390673603/10000000000 : ℝ)|^2111 ≤ (2764363314757/6250000000000 : ℝ)^1599
        have hw : |(5390673603/10000000000 : ℝ)|=(5390673603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s8_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2174775813/5000000000 : ℝ)*x 0 + (17485409/39062500 : ℝ)*x 1 + (2113170663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174775813/5000000000 : ℝ)^2111 ≤ (4164706334311/12500000000000 : ℝ)^1599 := by
    have hnat : (2174775813 : ℕ)^2111*12500000000000^1599 ≤ 4164706334311^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174775813 5000000000 4164706334311 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17485409/39062500 : ℝ)^2111 ≤ (34605007166657/100000000000000 : ℝ)^1599 := by
    have hnat : (17485409 : ℕ)^2111*100000000000000^1599 ≤ 34605007166657^1599*39062500^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17485409 39062500 34605007166657 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113170663/5000000000 : ℝ)^2111 ≤ (32077342146027/100000000000000 : ℝ)^1599 := by
    have hnat : (2113170663 : ℕ)^2111*100000000000000^1599 ≤ 32077342146027^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113170663 5000000000 32077342146027 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174775813/5000000000 : ℝ), (17485409/39062500 : ℝ), (2113170663/5000000000 : ℝ)] ![(4164706334311/12500000000000 : ℝ), (34605007166657/100000000000000 : ℝ), (32077342146027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174775813/5000000000 : ℝ)|^2111 ≤ (4164706334311/12500000000000 : ℝ)^1599
        have hw : |(2174775813/5000000000 : ℝ)|=(2174775813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17485409/39062500 : ℝ)|^2111 ≤ (34605007166657/100000000000000 : ℝ)^1599
        have hw : |(17485409/39062500 : ℝ)|=(17485409/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113170663/5000000000 : ℝ)|^2111 ≤ (32077342146027/100000000000000 : ℝ)^1599
        have hw : |(2113170663/5000000000 : ℝ)|=(2113170663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1149/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11489/100000 : ℝ) ^ (8443/2048 : ℝ) ≤ (13364675835596733/100000000000000000000 : ℝ) := by
    have hpowers : (11489/100000 : ℝ)^8443 ≤ (13364675835596733/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11489 : ℕ)^8443*100000000000000000000^2048 ≤ 13364675835596733^2048*100000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11489 100000 13364675835596733 100000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11489/100000 : ℝ)) (X := (13364675835596733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (8443/2048 : ℝ) ≤ (31170831555195517/100000000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^8443 ≤ (31170831555195517/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14109 : ℕ)^8443*100000000000000000000^2048 ≤ 31170831555195517^2048*100000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 31170831555195517 100000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (31170831555195517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013364675835596733/50000000000000000000 : ℝ) ≤ (625040518900033/625000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50013364675835596733/50000000000000000000 : ℝ)^2048 ≤ (625040518900033/625000000000000 : ℝ)^8443 := by
      have hnat : (50013364675835596733 : ℕ)^2048*625000000000000^8443 ≤ 625040518900033^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013364675835596733 50000000000000000000 625040518900033 625000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625040518900033/625000000000000 : ℝ)) (X := (50013364675835596733/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (400178142029563169/400000000000000000 : ℝ) ≤ (10001080105881797/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (400178142029563169/400000000000000000 : ℝ)^2048 ≤ (10001080105881797/10000000000000000 : ℝ)^8443 := by
      have hnat : (400178142029563169 : ℕ)^2048*10000000000000000^8443 ≤ 10001080105881797^8443*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400178142029563169 400000000000000000 10001080105881797 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001080105881797/10000000000000000 : ℝ)) (X := (400178142029563169/400000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031170831555195517/50000000000000000000 : ℝ) ≤ (5000755954681533/5000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50031170831555195517/50000000000000000000 : ℝ)^2048 ≤ (5000755954681533/5000000000000000 : ℝ)^8443 := by
      have hnat : (50031170831555195517 : ℕ)^2048*5000000000000000^8443 ≤ 5000755954681533^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031170831555195517 50000000000000000000 5000755954681533 5000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000755954681533/5000000000000000 : ℝ)) (X := (50031170831555195517/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13364675835596733/100000000000000000000 : ℝ) ≤ ((13095888285948392139/13100000000000000000 : ℝ)+2*(431803481269/262000000000000 : ℝ)*(11489/100000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (13095888285948392139/13100000000000000000 : ℝ)+2*(431803481269/262000000000000 : ℝ)*(11489/100000 : ℝ)=(625040518900033/625000000000000 : ℝ) by norm_num, show 1+2*(13364675835596733/100000000000000000000 : ℝ)=(50013364675835596733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31170831555195517/100000000000000000000 : ℝ)+(13364675835596733/100000000000000000000 : ℝ) ≤ ((13095888285948392139/13100000000000000000 : ℝ)+(431803481269/262000000000000 : ℝ)*((14109/100000 : ℝ)+(11489/100000 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (13095888285948392139/13100000000000000000 : ℝ)+(431803481269/262000000000000 : ℝ)*((14109/100000 : ℝ)+(11489/100000 : ℝ))=(10001080105881797/10000000000000000 : ℝ) by norm_num, show 1+(31170831555195517/100000000000000000000 : ℝ)+(13364675835596733/100000000000000000000 : ℝ)=(400178142029563169/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31170831555195517/100000000000000000000 : ℝ) ≤ ((13095888285948392139/13100000000000000000 : ℝ)+2*(431803481269/262000000000000 : ℝ)*(14109/100000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (13095888285948392139/13100000000000000000 : ℝ)+2*(431803481269/262000000000000 : ℝ)*(14109/100000 : ℝ)=(5000755954681533/5000000000000000 : ℝ) by norm_num, show 1+2*(31170831555195517/100000000000000000000 : ℝ)=(50031170831555195517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13095888285948392139/13100000000000000000 : ℝ)*(X 1 0+X 2 0)+(431803481269/262000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (13095888285948392139/13100000000000000000 : ℝ)) (alpha := (431803481269/262000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13095888285948392139/13100000000000000000 : ℝ)*(X 0 1+X 2 1)+(431803481269/262000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (13095888285948392139/13100000000000000000 : ℝ)) (alpha := (431803481269/262000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13095888285948392139/13100000000000000000 : ℝ)*(X 0 2+X 1 2)+(431803481269/262000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (13095888285948392139/13100000000000000000 : ℝ)) (alpha := (431803481269/262000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528957473/2500000000 : ℝ)*X 0 0+(5390986327/10000000000 : ℝ)*X 0 1+(5267374039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344249717/10000000000 : ℝ)*X 1 0+(-2178501883/10000000000 : ℝ)*X 1 1+(5267373987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068849937/2000000000 : ℝ)*X 2 0+(5267374023/10000000000 : ℝ)*X 2 1+(-1089250939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349542367/10000000000 : ℝ)*X 0 0+(1056426427/2500000000 : ℝ)*X 0 1+(4476897881/10000000000 : ℝ)*X 0 2+(4349542367/10000000000 : ℝ)*X 1 0+(1056426427/2500000000 : ℝ)*X 1 1+(4476897881/10000000000 : ℝ)*X 1 2+(4349542367/10000000000 : ℝ)*X 2 0+(1056426427/2500000000 : ℝ)*X 2 1+(4476897881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423166873/2000000000 : ℝ)*X 0 0+(1316921437/2500000000 : ℝ)*X 0 1+(5390673603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2174775813/5000000000 : ℝ)*X 0 0+(17485409/39062500 : ℝ)*X 0 1+(2113170663/5000000000 : ℝ)*X 0 2+(2174775813/5000000000 : ℝ)*X 1 0+(17485409/39062500 : ℝ)*X 1 1+(2113170663/5000000000 : ℝ)*X 1 2+(2174775813/5000000000 : ℝ)*X 2 0+(17485409/39062500 : ℝ)*X 2 1+(2113170663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (839158401126219039264948741/163750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (492895551/50000000000000 : ℝ)*(base19) + (857278657/100000000000000 : ℝ)*(base23) + (8558541/20000000000000 : ℝ)*(lower2) + (12240473/10000000000000 : ℝ)*(upper3) + (63339507/100000000000000 : ℝ)*(upper5) + (3017726082189027/50000000000000 : ℝ)*(major0) + (3017726082189027/50000000000000 : ℝ)*(major1) + (3017726082189027/50000000000000 : ℝ)*(major2) + (323593488281673/4000000000000 : ℝ)*(sp0) + (8089860719800481/100000000000000 : ℝ)*(sp1) + (8089860848312927/100000000000000 : ℝ)*(sp2) + (796205674532803/20000000000000 : ℝ)*(sp3) + (12249274879/50000000000000 : ℝ)*(sp4) + (2815935891/20000000000000 : ℝ)*(sp5) + (398104245234347/10000000000000 : ℝ)*(f.failure) + (252808178299737/3125000000000 : ℝ)*(f.sum) + (18180733175487/6550000000000000000000000000 : ℝ)*base66 + (5143402175037008753/655000000000000000000000000000000 : ℝ)*base67 + (440895767812008753/655000000000000000000000000000000 : ℝ)*base69 + (1451591934022008753/655000000000000000000000000000000 : ℝ)*base71 + (7530981013913/6550000000000000000000000000 : ℝ)*base73 + (293737901622008753/655000000000000000000000000000000 : ℝ)*base75 + (2491812063267991247/655000000000000000000000000000000 : ℝ)*base78 + (4175757861927008753/655000000000000000000000000000000 : ℝ)*base79 + (30574196950187/6550000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2141923/500000000000000000000 : ℝ)*base89 + (2141923/500000000000000000000 : ℝ)*base91 + (2141923/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1251_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1251_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1251_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1251_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1251_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1251_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1149/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
