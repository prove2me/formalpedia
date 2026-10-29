-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c321054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:41:24.232749+00:00
-- url     : https://prove2.me/submissions/9d4cc64c-f7b9-41a7-a2c5-13fbdb41dfcc

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
theorem collision_support_c321054_s1_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-197754311/2500000000 : ℝ)*x 0 + (4555090053/10000000000 : ℝ)*x 1 + (-3218027657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197754311/2500000000 : ℝ)^83 ≤ (4315848371769/100000000000000 : ℝ)^67 := by
    have hnat : (197754311 : ℕ)^83*100000000000000^67 ≤ 4315848371769^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197754311 2500000000 4315848371769 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555090053/10000000000 : ℝ)^83 ≤ (18876175590157/50000000000000 : ℝ)^67 := by
    have hnat : (4555090053 : ℕ)^83*50000000000000^67 ≤ 18876175590157^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555090053 10000000000 18876175590157 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3218027657/5000000000 : ℝ)^83 ≤ (5793180043709/10000000000000 : ℝ)^67 := by
    have hnat : (3218027657 : ℕ)^83*10000000000000^67 ≤ 5793180043709^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3218027657 5000000000 5793180043709 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197754311/2500000000 : ℝ), (4555090053/10000000000 : ℝ), (-3218027657/5000000000 : ℝ)] ![(4315848371769/100000000000000 : ℝ), (18876175590157/50000000000000 : ℝ), (5793180043709/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197754311/2500000000 : ℝ)|^83 ≤ (4315848371769/100000000000000 : ℝ)^67
        have hw : |(-197754311/2500000000 : ℝ)|=(197754311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555090053/10000000000 : ℝ)|^83 ≤ (18876175590157/50000000000000 : ℝ)^67
        have hw : |(4555090053/10000000000 : ℝ)|=(4555090053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3218027657/5000000000 : ℝ)|^83 ≤ (5793180043709/10000000000000 : ℝ)^67
        have hw : |(-3218027657/5000000000 : ℝ)|=(3218027657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1311947377/2500000000 : ℝ)*x 0 + (1302551731/2500000000 : ℝ)*x 1 + (-805748873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311947377/2500000000 : ℝ)^83 ≤ (8997774333601/20000000000000 : ℝ)^67 := by
    have hnat : (1311947377 : ℕ)^83*20000000000000^67 ≤ 8997774333601^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311947377 2500000000 8997774333601 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302551731/2500000000 : ℝ)^83 ≤ (22295039845827/50000000000000 : ℝ)^67 := by
    have hnat : (1302551731 : ℕ)^83*50000000000000^67 ≤ 22295039845827^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302551731 2500000000 22295039845827 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805748873/5000000000 : ℝ)^83 ≤ (521052431301/5000000000000 : ℝ)^67 := by
    have hnat : (805748873 : ℕ)^83*5000000000000^67 ≤ 521052431301^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805748873 5000000000 521052431301 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311947377/2500000000 : ℝ), (1302551731/2500000000 : ℝ), (-805748873/5000000000 : ℝ)] ![(8997774333601/20000000000000 : ℝ), (22295039845827/50000000000000 : ℝ), (521052431301/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311947377/2500000000 : ℝ)|^83 ≤ (8997774333601/20000000000000 : ℝ)^67
        have hw : |(1311947377/2500000000 : ℝ)|=(1311947377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302551731/2500000000 : ℝ)|^83 ≤ (22295039845827/50000000000000 : ℝ)^67
        have hw : |(1302551731/2500000000 : ℝ)|=(1302551731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-805748873/5000000000 : ℝ)|^83 ≤ (521052431301/5000000000000 : ℝ)^67
        have hw : |(-805748873/5000000000 : ℝ)|=(805748873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-37974903/625000000 : ℝ)*x 0 + (829245019/2000000000 : ℝ)*x 1 + (-55297317/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37974903/625000000 : ℝ)^83 ≤ (1556349231729/50000000000000 : ℝ)^67 := by
    have hnat : (37974903 : ℕ)^83*50000000000000^67 ≤ 1556349231729^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37974903 625000000 1556349231729 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829245019/2000000000 : ℝ)^83 ≤ (33600527845069/100000000000000 : ℝ)^67 := by
    have hnat : (829245019 : ℕ)^83*100000000000000^67 ≤ 33600527845069^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829245019 2000000000 33600527845069 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55297317/80000000 : ℝ)^83 ≤ (63286773679729/100000000000000 : ℝ)^67 := by
    have hnat : (55297317 : ℕ)^83*100000000000000^67 ≤ 63286773679729^67*80000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55297317 80000000 63286773679729 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37974903/625000000 : ℝ), (829245019/2000000000 : ℝ), (-55297317/80000000 : ℝ)] ![(1556349231729/50000000000000 : ℝ), (33600527845069/100000000000000 : ℝ), (63286773679729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37974903/625000000 : ℝ)|^83 ≤ (1556349231729/50000000000000 : ℝ)^67
        have hw : |(-37974903/625000000 : ℝ)|=(37974903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829245019/2000000000 : ℝ)|^83 ≤ (33600527845069/100000000000000 : ℝ)^67
        have hw : |(829245019/2000000000 : ℝ)|=(829245019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55297317/80000000 : ℝ)|^83 ≤ (63286773679729/100000000000000 : ℝ)^67
        have hw : |(-55297317/80000000 : ℝ)|=(55297317/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (324395513/625000000 : ℝ)*x 0 + (-3311727/40000000 : ℝ)*x 1 + (-1452955007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324395513/625000000 : ℝ)^83 ≤ (11094855561951/25000000000000 : ℝ)^67 := by
    have hnat : (324395513 : ℕ)^83*25000000000000^67 ≤ 11094855561951^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324395513 625000000 11094855561951 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3311727/40000000 : ℝ)^83 ≤ (4566728294901/100000000000000 : ℝ)^67 := by
    have hnat : (3311727 : ℕ)^83*100000000000000^67 ≤ 4566728294901^67*40000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311727 40000000 4566728294901 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1452955007/2500000000 : ℝ)^83 ≤ (2552692472001/5000000000000 : ℝ)^67 := by
    have hnat : (1452955007 : ℕ)^83*5000000000000^67 ≤ 2552692472001^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452955007 2500000000 2552692472001 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324395513/625000000 : ℝ), (-3311727/40000000 : ℝ), (-1452955007/2500000000 : ℝ)] ![(11094855561951/25000000000000 : ℝ), (4566728294901/100000000000000 : ℝ), (2552692472001/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324395513/625000000 : ℝ)|^83 ≤ (11094855561951/25000000000000 : ℝ)^67
        have hw : |(324395513/625000000 : ℝ)|=(324395513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3311727/40000000 : ℝ)|^83 ≤ (4566728294901/100000000000000 : ℝ)^67
        have hw : |(-3311727/40000000 : ℝ)|=(3311727/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1452955007/2500000000 : ℝ)|^83 ≤ (2552692472001/5000000000000 : ℝ)^67
        have hw : |(-1452955007/2500000000 : ℝ)|=(1452955007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4723439479/10000000000 : ℝ)*x 0 + (1587694081/2500000000 : ℝ)*x 1 + (134485379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4723439479/10000000000 : ℝ)^83 ≤ (9872094735107/25000000000000 : ℝ)^67 := by
    have hnat : (4723439479 : ℕ)^83*25000000000000^67 ≤ 9872094735107^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4723439479 10000000000 9872094735107 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1587694081/2500000000 : ℝ)^83 ≤ (28491196508583/50000000000000 : ℝ)^67 := by
    have hnat : (1587694081 : ℕ)^83*50000000000000^67 ≤ 28491196508583^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587694081 2500000000 28491196508583 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134485379/2000000000 : ℝ)^83 ≤ (1764614017517/50000000000000 : ℝ)^67 := by
    have hnat : (134485379 : ℕ)^83*50000000000000^67 ≤ 1764614017517^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134485379 2000000000 1764614017517 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4723439479/10000000000 : ℝ), (1587694081/2500000000 : ℝ), (134485379/2000000000 : ℝ)] ![(9872094735107/25000000000000 : ℝ), (28491196508583/50000000000000 : ℝ), (1764614017517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4723439479/10000000000 : ℝ)|^83 ≤ (9872094735107/25000000000000 : ℝ)^67
        have hw : |(4723439479/10000000000 : ℝ)|=(4723439479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1587694081/2500000000 : ℝ)|^83 ≤ (28491196508583/50000000000000 : ℝ)^67
        have hw : |(1587694081/2500000000 : ℝ)|=(1587694081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134485379/2000000000 : ℝ)|^83 ≤ (1764614017517/50000000000000 : ℝ)^67
        have hw : |(134485379/2000000000 : ℝ)|=(134485379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4921732207/10000000000 : ℝ)*x 0 + (3140428583/5000000000 : ℝ)*x 1 + (-29133741/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4921732207/10000000000 : ℝ)^83 ≤ (2597011858749/6250000000000 : ℝ)^67 := by
    have hnat : (4921732207 : ℕ)^83*6250000000000^67 ≤ 2597011858749^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921732207 10000000000 2597011858749 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3140428583/5000000000 : ℝ)^83 ≤ (28103126161949/50000000000000 : ℝ)^67 := by
    have hnat : (3140428583 : ℕ)^83*50000000000000^67 ≤ 28103126161949^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140428583 5000000000 28103126161949 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29133741/625000000 : ℝ)^83 ≤ (1120778962353/50000000000000 : ℝ)^67 := by
    have hnat : (29133741 : ℕ)^83*50000000000000^67 ≤ 1120778962353^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29133741 625000000 1120778962353 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4921732207/10000000000 : ℝ), (3140428583/5000000000 : ℝ), (-29133741/625000000 : ℝ)] ![(2597011858749/6250000000000 : ℝ), (28103126161949/50000000000000 : ℝ), (1120778962353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4921732207/10000000000 : ℝ)|^83 ≤ (2597011858749/6250000000000 : ℝ)^67
        have hw : |(4921732207/10000000000 : ℝ)|=(4921732207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3140428583/5000000000 : ℝ)|^83 ≤ (28103126161949/50000000000000 : ℝ)^67
        have hw : |(3140428583/5000000000 : ℝ)|=(3140428583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29133741/625000000 : ℝ)|^83 ≤ (1120778962353/50000000000000 : ℝ)^67
        have hw : |(-29133741/625000000 : ℝ)|=(29133741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-51085581/5000000000 : ℝ)*x 0 + (2258460761/5000000000 : ℝ)*x 1 + (-6824786479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51085581/5000000000 : ℝ)^83 ≤ (341935391341/100000000000000 : ℝ)^67 := by
    have hnat : (51085581 : ℕ)^83*100000000000000^67 ≤ 341935391341^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51085581 5000000000 341935391341 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258460761/5000000000 : ℝ)^83 ≤ (9340215422391/25000000000000 : ℝ)^67 := by
    have hnat : (2258460761 : ℕ)^83*25000000000000^67 ≤ 9340215422391^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258460761 5000000000 9340215422391 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6824786479/10000000000 : ℝ)^83 ≤ (31148601450873/50000000000000 : ℝ)^67 := by
    have hnat : (6824786479 : ℕ)^83*50000000000000^67 ≤ 31148601450873^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6824786479 10000000000 31148601450873 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51085581/5000000000 : ℝ), (2258460761/5000000000 : ℝ), (-6824786479/10000000000 : ℝ)] ![(341935391341/100000000000000 : ℝ), (9340215422391/25000000000000 : ℝ), (31148601450873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51085581/5000000000 : ℝ)|^83 ≤ (341935391341/100000000000000 : ℝ)^67
        have hw : |(-51085581/5000000000 : ℝ)|=(51085581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258460761/5000000000 : ℝ)|^83 ≤ (9340215422391/25000000000000 : ℝ)^67
        have hw : |(2258460761/5000000000 : ℝ)|=(2258460761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6824786479/10000000000 : ℝ)|^83 ≤ (31148601450873/50000000000000 : ℝ)^67
        have hw : |(-6824786479/10000000000 : ℝ)|=(6824786479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4853958759/10000000000 : ℝ)*x 0 + (-331094947/2500000000 : ℝ)*x 1 + (-2902662257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4853958759/10000000000 : ℝ)^83 ≤ (8168906930329/20000000000000 : ℝ)^67 := by
    have hnat : (4853958759 : ℕ)^83*20000000000000^67 ≤ 8168906930329^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4853958759 10000000000 8168906930329 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331094947/2500000000 : ℝ)^83 ≤ (1634458483503/20000000000000 : ℝ)^67 := by
    have hnat : (331094947 : ℕ)^83*20000000000000^67 ≤ 1634458483503^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331094947 2500000000 1634458483503 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2902662257/5000000000 : ℝ)^83 ≤ (25491586458801/50000000000000 : ℝ)^67 := by
    have hnat : (2902662257 : ℕ)^83*50000000000000^67 ≤ 25491586458801^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902662257 5000000000 25491586458801 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4853958759/10000000000 : ℝ), (-331094947/2500000000 : ℝ), (-2902662257/5000000000 : ℝ)] ![(8168906930329/20000000000000 : ℝ), (1634458483503/20000000000000 : ℝ), (25491586458801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4853958759/10000000000 : ℝ)|^83 ≤ (8168906930329/20000000000000 : ℝ)^67
        have hw : |(4853958759/10000000000 : ℝ)|=(4853958759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331094947/2500000000 : ℝ)|^83 ≤ (1634458483503/20000000000000 : ℝ)^67
        have hw : |(-331094947/2500000000 : ℝ)|=(331094947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2902662257/5000000000 : ℝ)|^83 ≤ (25491586458801/50000000000000 : ℝ)^67
        have hw : |(-2902662257/5000000000 : ℝ)|=(2902662257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6397388617/10000000000 : ℝ)*x 0 + (933842417/2000000000 : ℝ)*x 1 + (339460891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6397388617/10000000000 : ℝ)^83 ≤ (7187618879641/12500000000000 : ℝ)^67 := by
    have hnat : (6397388617 : ℕ)^83*12500000000000^67 ≤ 7187618879641^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6397388617 10000000000 7187618879641 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933842417/2000000000 : ℝ)^83 ≤ (9731885862829/25000000000000 : ℝ)^67 := by
    have hnat : (933842417 : ℕ)^83*25000000000000^67 ≤ 9731885862829^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933842417 2000000000 9731885862829 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339460891/5000000000 : ℝ)^83 ≤ (71430109917/2000000000000 : ℝ)^67 := by
    have hnat : (339460891 : ℕ)^83*2000000000000^67 ≤ 71430109917^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339460891 5000000000 71430109917 2000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6397388617/10000000000 : ℝ), (933842417/2000000000 : ℝ), (339460891/5000000000 : ℝ)] ![(7187618879641/12500000000000 : ℝ), (9731885862829/25000000000000 : ℝ), (71430109917/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6397388617/10000000000 : ℝ)|^83 ≤ (7187618879641/12500000000000 : ℝ)^67
        have hw : |(6397388617/10000000000 : ℝ)|=(6397388617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933842417/2000000000 : ℝ)|^83 ≤ (9731885862829/25000000000000 : ℝ)^67
        have hw : |(933842417/2000000000 : ℝ)|=(933842417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339460891/5000000000 : ℝ)|^83 ≤ (71430109917/2000000000000 : ℝ)^67
        have hw : |(339460891/5000000000 : ℝ)|=(339460891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3100309759/5000000000 : ℝ)*x 0 + (2429517267/5000000000 : ℝ)*x 1 + (-711412537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3100309759/5000000000 : ℝ)^83 ≤ (6914763878523/12500000000000 : ℝ)^67 := by
    have hnat : (3100309759 : ℕ)^83*12500000000000^67 ≤ 6914763878523^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3100309759 5000000000 6914763878523 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2429517267/5000000000 : ℝ)^83 ≤ (20448725979071/50000000000000 : ℝ)^67 := by
    have hnat : (2429517267 : ℕ)^83*50000000000000^67 ≤ 20448725979071^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429517267 5000000000 20448725979071 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711412537/10000000000 : ℝ)^83 ≤ (3784436992121/100000000000000 : ℝ)^67 := by
    have hnat : (711412537 : ℕ)^83*100000000000000^67 ≤ 3784436992121^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711412537 10000000000 3784436992121 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3100309759/5000000000 : ℝ), (2429517267/5000000000 : ℝ), (-711412537/10000000000 : ℝ)] ![(6914763878523/12500000000000 : ℝ), (20448725979071/50000000000000 : ℝ), (3784436992121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3100309759/5000000000 : ℝ)|^83 ≤ (6914763878523/12500000000000 : ℝ)^67
        have hw : |(3100309759/5000000000 : ℝ)|=(3100309759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2429517267/5000000000 : ℝ)|^83 ≤ (20448725979071/50000000000000 : ℝ)^67
        have hw : |(2429517267/5000000000 : ℝ)|=(2429517267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-711412537/10000000000 : ℝ)|^83 ≤ (3784436992121/100000000000000 : ℝ)^67
        have hw : |(-711412537/10000000000 : ℝ)|=(711412537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1312587/1000000000 : ℝ)*x 0 + (2646305051/5000000000 : ℝ)*x 1 + (-3063595079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312587/1000000000 : ℝ)^83 ≤ (26910383281/100000000000000 : ℝ)^67 := by
    have hnat : (1312587 : ℕ)^83*100000000000000^67 ≤ 26910383281^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312587 1000000000 26910383281 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2646305051/5000000000 : ℝ)^83 ≤ (45465358941713/100000000000000 : ℝ)^67 := by
    have hnat : (2646305051 : ℕ)^83*100000000000000^67 ≤ 45465358941713^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646305051 5000000000 45465358941713 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3063595079/5000000000 : ℝ)^83 ≤ (27253865334969/50000000000000 : ℝ)^67 := by
    have hnat : (3063595079 : ℕ)^83*50000000000000^67 ≤ 27253865334969^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3063595079 5000000000 27253865334969 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1312587/1000000000 : ℝ), (2646305051/5000000000 : ℝ), (-3063595079/5000000000 : ℝ)] ![(26910383281/100000000000000 : ℝ), (45465358941713/100000000000000 : ℝ), (27253865334969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1312587/1000000000 : ℝ)|^83 ≤ (26910383281/100000000000000 : ℝ)^67
        have hw : |(-1312587/1000000000 : ℝ)|=(1312587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2646305051/5000000000 : ℝ)|^83 ≤ (45465358941713/100000000000000 : ℝ)^67
        have hw : |(2646305051/5000000000 : ℝ)|=(2646305051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3063595079/5000000000 : ℝ)|^83 ≤ (27253865334969/50000000000000 : ℝ)^67
        have hw : |(-3063595079/5000000000 : ℝ)|=(3063595079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3214338609/5000000000 : ℝ)*x 0 + (-1209162061/10000000000 : ℝ)*x 1 + (-170808081/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3214338609/5000000000 : ℝ)^83 ≤ (14462385266639/25000000000000 : ℝ)^67 := by
    have hnat : (3214338609 : ℕ)^83*25000000000000^67 ≤ 14462385266639^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3214338609 5000000000 14462385266639 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209162061/10000000000 : ℝ)^83 ≤ (912612365523/12500000000000 : ℝ)^67 := by
    have hnat : (1209162061 : ℕ)^83*12500000000000^67 ≤ 912612365523^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209162061 10000000000 912612365523 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170808081/400000000 : ℝ)^83 ≤ (1742477999583/5000000000000 : ℝ)^67 := by
    have hnat : (170808081 : ℕ)^83*5000000000000^67 ≤ 1742477999583^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170808081 400000000 1742477999583 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3214338609/5000000000 : ℝ), (-1209162061/10000000000 : ℝ), (-170808081/400000000 : ℝ)] ![(14462385266639/25000000000000 : ℝ), (912612365523/12500000000000 : ℝ), (1742477999583/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3214338609/5000000000 : ℝ)|^83 ≤ (14462385266639/25000000000000 : ℝ)^67
        have hw : |(3214338609/5000000000 : ℝ)|=(3214338609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1209162061/10000000000 : ℝ)|^83 ≤ (912612365523/12500000000000 : ℝ)^67
        have hw : |(-1209162061/10000000000 : ℝ)|=(1209162061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170808081/400000000 : ℝ)|^83 ≤ (1742477999583/5000000000000 : ℝ)^67
        have hw : |(-170808081/400000000 : ℝ)|=(170808081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4999295943/10000000000 : ℝ)*x 0 + (5375521331/10000000000 : ℝ)*x 1 + (171860089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4999295943/10000000000 : ℝ)^83 ≤ (4236492885153/10000000000000 : ℝ)^67 := by
    have hnat : (4999295943 : ℕ)^83*10000000000000^67 ≤ 4236492885153^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999295943 10000000000 4236492885153 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375521331/10000000000 : ℝ)^83 ≤ (5793665667067/12500000000000 : ℝ)^67 := by
    have hnat : (5375521331 : ℕ)^83*12500000000000^67 ≤ 5793665667067^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375521331 10000000000 5793665667067 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171860089/1000000000 : ℝ)^83 ≤ (5642872899607/50000000000000 : ℝ)^67 := by
    have hnat : (171860089 : ℕ)^83*50000000000000^67 ≤ 5642872899607^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171860089 1000000000 5642872899607 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4999295943/10000000000 : ℝ), (5375521331/10000000000 : ℝ), (171860089/1000000000 : ℝ)] ![(4236492885153/10000000000000 : ℝ), (5793665667067/12500000000000 : ℝ), (5642872899607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4999295943/10000000000 : ℝ)|^83 ≤ (4236492885153/10000000000000 : ℝ)^67
        have hw : |(4999295943/10000000000 : ℝ)|=(4999295943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375521331/10000000000 : ℝ)|^83 ≤ (5793665667067/12500000000000 : ℝ)^67
        have hw : |(5375521331/10000000000 : ℝ)|=(5375521331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171860089/1000000000 : ℝ)|^83 ≤ (5642872899607/50000000000000 : ℝ)^67
        have hw : |(171860089/1000000000 : ℝ)|=(171860089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321054_s1_s1_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5954777373/10000000000 : ℝ)*x 0 + (4730364749/10000000000 : ℝ)*x 1 + (-1278863537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5954777373/10000000000 : ℝ)^83 ≤ (52614091267631/100000000000000 : ℝ)^67 := by
    have hnat : (5954777373 : ℕ)^83*100000000000000^67 ≤ 52614091267631^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954777373 10000000000 52614091267631 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4730364749/10000000000 : ℝ)^83 ≤ (19780056626777/50000000000000 : ℝ)^67 := by
    have hnat : (4730364749 : ℕ)^83*50000000000000^67 ≤ 19780056626777^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730364749 10000000000 19780056626777 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278863537/10000000000 : ℝ)^83 ≤ (7825795459159/100000000000000 : ℝ)^67 := by
    have hnat : (1278863537 : ℕ)^83*100000000000000^67 ≤ 7825795459159^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278863537 10000000000 7825795459159 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5954777373/10000000000 : ℝ), (4730364749/10000000000 : ℝ), (-1278863537/10000000000 : ℝ)] ![(52614091267631/100000000000000 : ℝ), (19780056626777/50000000000000 : ℝ), (7825795459159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5954777373/10000000000 : ℝ)|^83 ≤ (52614091267631/100000000000000 : ℝ)^67
        have hw : |(5954777373/10000000000 : ℝ)|=(5954777373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4730364749/10000000000 : ℝ)|^83 ≤ (19780056626777/50000000000000 : ℝ)^67
        have hw : |(4730364749/10000000000 : ℝ)|=(4730364749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1278863537/10000000000 : ℝ)|^83 ≤ (7825795459159/100000000000000 : ℝ)^67
        have hw : |(-1278863537/10000000000 : ℝ)|=(1278863537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321054_s1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((34483/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34483/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-32093/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-32093/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((843/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31831/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31831/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (34483/50000 : ℝ) ^ (81/16 : ℝ) ≤ (3810920487793926609/25000000000000000000 : ℝ) := by
    have hpowers : (34483/50000 : ℝ)^81 ≤ (3810920487793926609/25000000000000000000 : ℝ)^16 := by
      have hnat : (34483 : ℕ)^81*25000000000000000000^16 ≤ 3810920487793926609^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34483 50000 3810920487793926609 25000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34483/50000 : ℝ)) (X := (3810920487793926609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (28810920487793926609/25000000000000000000 : ℝ) ≤ (1028421823576761/1000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (28810920487793926609/25000000000000000000 : ℝ)^16 ≤ (1028421823576761/1000000000000000 : ℝ)^81 := by
      have hnat : (28810920487793926609 : ℕ)^16*1000000000000000^81 ≤ 1028421823576761^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28810920487793926609 25000000000000000000 1028421823576761 1000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1028421823576761/1000000000000000 : ℝ)) (X := (28810920487793926609/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (16310920487793926609/12500000000000000000 : ℝ) ≤ (2634925533492251/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (16310920487793926609/12500000000000000000 : ℝ)^16 ≤ (2634925533492251/2500000000000000 : ℝ)^81 := by
      have hnat : (16310920487793926609 : ℕ)^16*2500000000000000^81 ≤ 2634925533492251^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16310920487793926609 12500000000000000000 2634925533492251 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2634925533492251/2500000000000000 : ℝ)) (X := (16310920487793926609/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(28421823576761/689660000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(127741949100697/3448300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (34483/50000 : ℝ)) (alpha := (28421823576761/689660000000000 : ℝ)) (beta := (127741949100697/3448300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (34483/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(28421823576761/689660000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(127741949100697/3448300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (36317/50000 : ℝ) ^ (81/16 : ℝ) ≤ (19816230992187627171/100000000000000000000 : ℝ) := by
    have hpowers : (36317/50000 : ℝ)^81 ≤ (19816230992187627171/100000000000000000000 : ℝ)^16 := by
      have hnat : (36317 : ℕ)^81*100000000000000000000^16 ≤ 19816230992187627171^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36317 50000 19816230992187627171 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36317/50000 : ℝ)) (X := (19816230992187627171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (119816230992187627171/100000000000000000000 : ℝ) ≤ (10363567132561927/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (119816230992187627171/100000000000000000000 : ℝ)^16 ≤ (10363567132561927/10000000000000000 : ℝ)^81 := by
      have hnat : (119816230992187627171 : ℕ)^16*10000000000000000^81 ≤ 10363567132561927^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119816230992187627171 100000000000000000000 10363567132561927 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10363567132561927/10000000000000000 : ℝ)) (X := (119816230992187627171/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (69816230992187627171/50000000000000000000 : ℝ) ≤ (5340836614411697/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (69816230992187627171/50000000000000000000 : ℝ)^16 ≤ (5340836614411697/5000000000000000 : ℝ)^81 := by
      have hnat : (69816230992187627171 : ℕ)^16*5000000000000000^81 ≤ 5340836614411697^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69816230992187627171 50000000000000000000 5340836614411697 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5340836614411697/5000000000000000 : ℝ)) (X := (69816230992187627171/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(363567132561927/7263400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(318106096261467/7263400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (36317/50000 : ℝ)) (alpha := (363567132561927/7263400000000000 : ℝ)) (beta := (318106096261467/7263400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (36317/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(363567132561927/7263400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(318106096261467/7263400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (32093/50000 : ℝ) ^ (81/16 : ℝ) ≤ (10596600914193240479/100000000000000000000 : ℝ) := by
    have hpowers : (32093/50000 : ℝ)^81 ≤ (10596600914193240479/100000000000000000000 : ℝ)^16 := by
      have hnat : (32093 : ℕ)^81*100000000000000000000^16 ≤ 10596600914193240479^16*50000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32093 50000 10596600914193240479 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32093/50000 : ℝ)) (X := (10596600914193240479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110596600914193240479/100000000000000000000 : ℝ) ≤ (2550235930010997/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (110596600914193240479/100000000000000000000 : ℝ)^16 ≤ (2550235930010997/2500000000000000 : ℝ)^81 := by
      have hnat : (110596600914193240479 : ℕ)^16*2500000000000000^81 ≤ 2550235930010997^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110596600914193240479 100000000000000000000 2550235930010997 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2550235930010997/2500000000000000 : ℝ)) (X := (110596600914193240479/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60596600914193240479/50000000000000000000 : ℝ) ≤ (10386985675875759/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (60596600914193240479/50000000000000000000 : ℝ)^16 ≤ (10386985675875759/10000000000000000 : ℝ)^81 := by
      have hnat : (60596600914193240479 : ℕ)^16*10000000000000000^81 ≤ 10386985675875759^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60596600914193240479 50000000000000000000 10386985675875759 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10386985675875759/10000000000000000 : ℝ)) (X := (60596600914193240479/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(50235930010997/1604650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(186041955831771/6418600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (32093/50000 : ℝ)) (alpha := (50235930010997/1604650000000000 : ℝ)) (beta := (186041955831771/6418600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (32093/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(50235930010997/1604650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(186041955831771/6418600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-197754311/2500000000 : ℝ)*X 0 0+(4555090053/10000000000 : ℝ)*X 0 1+(-3218027657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1311947377/2500000000 : ℝ)*X 0 0+(1302551731/2500000000 : ℝ)*X 0 1+(-805748873/5000000000 : ℝ)*X 0 2+(1311947377/2500000000 : ℝ)*X 1 0+(1302551731/2500000000 : ℝ)*X 1 1+(-805748873/5000000000 : ℝ)*X 1 2+(1311947377/2500000000 : ℝ)*X 2 0+(1302551731/2500000000 : ℝ)*X 2 1+(-805748873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-37974903/625000000 : ℝ)*X 0 0+(829245019/2000000000 : ℝ)*X 0 1+(-55297317/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((324395513/625000000 : ℝ)*X 1 0+(-3311727/40000000 : ℝ)*X 1 1+(-1452955007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4723439479/10000000000 : ℝ)*X 2 0+(1587694081/2500000000 : ℝ)*X 2 1+(134485379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4921732207/10000000000 : ℝ)*X 0 0+(3140428583/5000000000 : ℝ)*X 0 1+(-29133741/625000000 : ℝ)*X 0 2+(4921732207/10000000000 : ℝ)*X 1 0+(3140428583/5000000000 : ℝ)*X 1 1+(-29133741/625000000 : ℝ)*X 1 2+(4921732207/10000000000 : ℝ)*X 2 0+(3140428583/5000000000 : ℝ)*X 2 1+(-29133741/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-51085581/5000000000 : ℝ)*X 0 0+(2258460761/5000000000 : ℝ)*X 0 1+(-6824786479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4853958759/10000000000 : ℝ)*X 1 0+(-331094947/2500000000 : ℝ)*X 1 1+(-2902662257/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6397388617/10000000000 : ℝ)*X 2 0+(933842417/2000000000 : ℝ)*X 2 1+(339460891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3100309759/5000000000 : ℝ)*X 0 0+(2429517267/5000000000 : ℝ)*X 0 1+(-711412537/10000000000 : ℝ)*X 0 2+(3100309759/5000000000 : ℝ)*X 1 0+(2429517267/5000000000 : ℝ)*X 1 1+(-711412537/10000000000 : ℝ)*X 1 2+(3100309759/5000000000 : ℝ)*X 2 0+(2429517267/5000000000 : ℝ)*X 2 1+(-711412537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1312587/1000000000 : ℝ)*X 0 0+(2646305051/5000000000 : ℝ)*X 0 1+(-3063595079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3214338609/5000000000 : ℝ)*X 1 0+(-1209162061/10000000000 : ℝ)*X 1 1+(-170808081/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4999295943/10000000000 : ℝ)*X 2 0+(5375521331/10000000000 : ℝ)*X 2 1+(171860089/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((5954777373/10000000000 : ℝ)*X 0 0+(4730364749/10000000000 : ℝ)*X 0 1+(-1278863537/10000000000 : ℝ)*X 0 2+(5954777373/10000000000 : ℝ)*X 1 0+(4730364749/10000000000 : ℝ)*X 1 1+(-1278863537/10000000000 : ℝ)*X 1 2+(5954777373/10000000000 : ℝ)*X 2 0+(4730364749/10000000000 : ℝ)*X 2 1+(-1278863537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((843/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (50215930849455059500524223077627/4019067722932300000000000000000000000 : ℝ) := by norm_num
    linear_combination (15854381/1000000000000 : ℝ)*(base23) + (361442962207/1000000000000 : ℝ)*(base39) + (194431342123/500000000000 : ℝ)*(base60) + (4439115079479/1000000000000 : ℝ)*(major_s1_0) + (4439115079479/1000000000000 : ℝ)*(major_s1_1) + (4439115079479/1000000000000 : ℝ)*(major_s1_2) + (25411521/1000000000000 : ℝ)*(sp_s1_6) + (6546127350781/1000000000000 : ℝ)*(sp_s1_7) + (1309218402941/200000000000 : ℝ)*(sp_s1_8) + (6546120994849/1000000000000 : ℝ)*(sp_s1_9) + (36437976651/15625000000 : ℝ)*(sp_s1_13) + (42726181/1000000000000 : ℝ)*(sp_s1_14) + (78062257/1000000000000 : ℝ)*(sp_s1_15) + (8306933/250000000000 : ℝ)*(sp_s1_23) + (466411183437/200000000000 : ℝ)*(f.failure) + (3273085038481/500000000000 : ℝ)*(f.sum) + (116325894488292342767/233104296200000000000000000000000 : ℝ)*base62 + (382058496799991/6418600000000000000000000000 : ℝ)*base64 + (230203040045467/7263400000000000000000000000 : ℝ)*base67 + (112143590740659/200581250000000000000000000 : ℝ)*base68 + (729721705255784643/221332583800000000000000000000000 : ℝ)*base70 + (1209230675155903/3448300000000000000000000000 : ℝ)*base73 + (2518713217543387/7263400000000000000000000000 : ℝ)*base74 + (180405463492617/689660000000000000000000000 : ℝ)*base76 + (85694944791631132723/250463822200000000000000000000000 : ℝ)*base79 + (1239/1250000000000000 : ℝ)*base87 + (1239/1250000000000000 : ℝ)*base89 + (1239/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44457/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32265132880462991441366711363787/2009533861466150000000000000000000000 : ℝ) := by norm_num
    linear_combination (1738203/250000000000 : ℝ)*(base21) + (317199169367/1000000000000 : ℝ)*(base39) + (986881/250000000000 : ℝ)*(base49) + (46695720057/1000000000000 : ℝ)*(base60) + (4564443196531/1000000000000 : ℝ)*(major_s1_0) + (4564443196531/1000000000000 : ℝ)*(major_s1_1) + (4564443196531/1000000000000 : ℝ)*(major_s1_2) + (64802919/1000000000000 : ℝ)*(sp_s1_0) + (101815247/1000000000000 : ℝ)*(sp_s1_8) + (1346184026337/200000000000 : ℝ)*(sp_s1_14) + (3365441559679/500000000000 : ℝ)*(sp_s1_15) + (6730977981793/1000000000000 : ℝ)*(sp_s1_16) + (2397718601471/1000000000000 : ℝ)*(sp_s1_20) + (177504969/1000000000000 : ℝ)*(sp_s1_27) + (59947402661/25000000000 : ℝ)*(f.failure) + (1346196986921/200000000000 : ℝ)*(f.sum) + (84178018934868697463/233104296200000000000000000000000 : ℝ)*base62 + (6231910371282481/6418600000000000000000000000 : ℝ)*base65 + (8974264469658237/7263400000000000000000000000 : ℝ)*base66 + (174918763666069/802325000000000000000000000 : ℝ)*base68 + (90593055227958374733/221332583800000000000000000000000 : ℝ)*base71 + (1678045946413253/3448300000000000000000000000 : ℝ)*base72 + (944241580362597/7263400000000000000000000000 : ℝ)*base75 + (79394176109891/689660000000000000000000000 : ℝ)*base77 + (232710663912235538173/250463822200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (207/625000000000000 : ℝ)*base86 + (207/625000000000000 : ℝ)*base88 + (207/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31831/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31831/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5412327966390574565143203190833/502383465366537500000000000000000000 : ℝ) := by norm_num
    linear_combination (194619/250000000000 : ℝ)*(base11) + (6668851/1000000000000 : ℝ)*(base15) + (420423170311/500000000000 : ℝ)*(base39) + (2561783/1000000000000 : ℝ)*(base40) + (4356661252659/1000000000000 : ℝ)*(major_s1_0) + (4356661252659/1000000000000 : ℝ)*(major_s1_1) + (4356661252659/1000000000000 : ℝ)*(major_s1_2) + (1859633/62500000000 : ℝ)*(sp_s1_9) + (25029/25000000000 : ℝ)*(sp_s1_16) + (98009491/1000000000000 : ℝ)*(sp_s1_20) + (803072339999/125000000000 : ℝ)*(sp_s1_21) + (401535801851/62500000000 : ℝ)*(sp_s1_22) + (321227437159/50000000000 : ℝ)*(sp_s1_23) + (1144320703127/500000000000 : ℝ)*(sp_s1_27) + (457747883149/200000000000 : ℝ)*(f.failure) + (1606144874617/250000000000 : ℝ)*(f.sum) + (18366541410292652413/233104296200000000000000000000000 : ℝ)*base63 + (2203834643551551/6418600000000000000000000000 : ℝ)*base64 + (3683308506387587/7263400000000000000000000000 : ℝ)*base67 + (639365806279903/1604650000000000000000000000 : ℝ)*base69 + (49648047409554950263/221332583800000000000000000000000 : ℝ)*base70 + (2031836768779273/3448300000000000000000000000 : ℝ)*base73 + (2749702977387787/7263400000000000000000000000 : ℝ)*base74 + (432178620881373/689660000000000000000000000 : ℝ)*base76 + (86861057015487317783/250463822200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (97/1250000000000000 : ℝ)*base86 + (97/1250000000000000 : ℝ)*base88 + (97/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((34483/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34483/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-32093/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-32093/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((843/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31831/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31831/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c321054_s1 p hpa hpb X hX hprev0

#print axioms solution
