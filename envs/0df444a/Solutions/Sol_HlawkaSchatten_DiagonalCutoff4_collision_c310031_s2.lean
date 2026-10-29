-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310031_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:23:59.070944+00:00
-- url     : https://prove2.me/submissions/6aeb59c5-1164-4c00-9977-7e1ab3867702

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
theorem collision_support_c310031_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3538564871/10000000000 : ℝ)*x 0 + (5341043077/10000000000 : ℝ)*x 1 + (3823767191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3538564871/10000000000 : ℝ)^9 ≤ (26297873776639/100000000000000 : ℝ)^7 := by
    have hnat : (3538564871 : ℕ)^9*100000000000000^7 ≤ 26297873776639^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3538564871 10000000000 26297873776639 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5341043077/10000000000 : ℝ)^9 ≤ (44648303419817/100000000000000 : ℝ)^7 := by
    have hnat : (5341043077 : ℕ)^9*100000000000000^7 ≤ 44648303419817^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341043077 10000000000 44648303419817 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3823767191/10000000000 : ℝ)^9 ≤ (29053822786523/100000000000000 : ℝ)^7 := by
    have hnat : (3823767191 : ℕ)^9*100000000000000^7 ≤ 29053822786523^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3823767191 10000000000 29053822786523 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3538564871/10000000000 : ℝ), (5341043077/10000000000 : ℝ), (3823767191/10000000000 : ℝ)] ![(26297873776639/100000000000000 : ℝ), (44648303419817/100000000000000 : ℝ), (29053822786523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3538564871/10000000000 : ℝ)|^9 ≤ (26297873776639/100000000000000 : ℝ)^7
        have hw : |(-3538564871/10000000000 : ℝ)|=(3538564871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5341043077/10000000000 : ℝ)|^9 ≤ (44648303419817/100000000000000 : ℝ)^7
        have hw : |(5341043077/10000000000 : ℝ)|=(5341043077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3823767191/10000000000 : ℝ)|^9 ≤ (29053822786523/100000000000000 : ℝ)^7
        have hw : |(3823767191/10000000000 : ℝ)|=(3823767191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5740248447/10000000000 : ℝ)*x 0 + (-1208101051/10000000000 : ℝ)*x 1 + (5318992733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5740248447/10000000000 : ℝ)^9 ≤ (48983943327917/100000000000000 : ℝ)^7 := by
    have hnat : (5740248447 : ℕ)^9*100000000000000^7 ≤ 48983943327917^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5740248447 10000000000 48983943327917 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208101051/10000000000 : ℝ)^9 ≤ (6604608077239/100000000000000 : ℝ)^7 := by
    have hnat : (1208101051 : ℕ)^9*100000000000000^7 ≤ 6604608077239^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208101051 10000000000 6604608077239 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5318992733/10000000000 : ℝ)^9 ≤ (44411448586259/100000000000000 : ℝ)^7 := by
    have hnat : (5318992733 : ℕ)^9*100000000000000^7 ≤ 44411448586259^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5318992733 10000000000 44411448586259 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5740248447/10000000000 : ℝ), (-1208101051/10000000000 : ℝ), (5318992733/10000000000 : ℝ)] ![(48983943327917/100000000000000 : ℝ), (6604608077239/100000000000000 : ℝ), (44411448586259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5740248447/10000000000 : ℝ)|^9 ≤ (48983943327917/100000000000000 : ℝ)^7
        have hw : |(5740248447/10000000000 : ℝ)|=(5740248447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1208101051/10000000000 : ℝ)|^9 ≤ (6604608077239/100000000000000 : ℝ)^7
        have hw : |(-1208101051/10000000000 : ℝ)|=(1208101051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5318992733/10000000000 : ℝ)|^9 ≤ (44411448586259/100000000000000 : ℝ)^7
        have hw : |(5318992733/10000000000 : ℝ)|=(5318992733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3341981461/10000000000 : ℝ)*x 0 + (22809981/40000000 : ℝ)*x 1 + (-3611339493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3341981461/10000000000 : ℝ)^9 ≤ (6108649377361/25000000000000 : ℝ)^7 := by
    have hnat : (3341981461 : ℕ)^9*25000000000000^7 ≤ 6108649377361^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3341981461 10000000000 6108649377361 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22809981/40000000 : ℝ)^9 ≤ (24285061234147/50000000000000 : ℝ)^7 := by
    have hnat : (22809981 : ℕ)^9*50000000000000^7 ≤ 24285061234147^7*40000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22809981 40000000 24285061234147 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3611339493/10000000000 : ℝ)^9 ≤ (13497640002993/50000000000000 : ℝ)^7 := by
    have hnat : (3611339493 : ℕ)^9*50000000000000^7 ≤ 13497640002993^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611339493 10000000000 13497640002993 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3341981461/10000000000 : ℝ), (22809981/40000000 : ℝ), (-3611339493/10000000000 : ℝ)] ![(6108649377361/25000000000000 : ℝ), (24285061234147/50000000000000 : ℝ), (13497640002993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3341981461/10000000000 : ℝ)|^9 ≤ (6108649377361/25000000000000 : ℝ)^7
        have hw : |(3341981461/10000000000 : ℝ)|=(3341981461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22809981/40000000 : ℝ)|^9 ≤ (24285061234147/50000000000000 : ℝ)^7
        have hw : |(22809981/40000000 : ℝ)|=(22809981/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3611339493/10000000000 : ℝ)|^9 ≤ (13497640002993/50000000000000 : ℝ)^7
        have hw : |(-3611339493/10000000000 : ℝ)|=(3611339493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2035656603/5000000000 : ℝ)*x 0 + (2449354961/5000000000 : ℝ)*x 1 + (3772534509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035656603/5000000000 : ℝ)^9 ≤ (15747082169247/50000000000000 : ℝ)^7 := by
    have hnat : (2035656603 : ℕ)^9*50000000000000^7 ≤ 15747082169247^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035656603 5000000000 15747082169247 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2449354961/5000000000 : ℝ)^9 ≤ (399515510177/1000000000000 : ℝ)^7 := by
    have hnat : (2449354961 : ℕ)^9*1000000000000^7 ≤ 399515510177^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449354961 5000000000 399515510177 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3772534509/10000000000 : ℝ)^9 ≤ (892321394819/3125000000000 : ℝ)^7 := by
    have hnat : (3772534509 : ℕ)^9*3125000000000^7 ≤ 892321394819^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3772534509 10000000000 892321394819 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2035656603/5000000000 : ℝ), (2449354961/5000000000 : ℝ), (3772534509/10000000000 : ℝ)] ![(15747082169247/50000000000000 : ℝ), (399515510177/1000000000000 : ℝ), (892321394819/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2035656603/5000000000 : ℝ)|^9 ≤ (15747082169247/50000000000000 : ℝ)^7
        have hw : |(2035656603/5000000000 : ℝ)|=(2035656603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2449354961/5000000000 : ℝ)|^9 ≤ (399515510177/1000000000000 : ℝ)^7
        have hw : |(2449354961/5000000000 : ℝ)|=(2449354961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3772534509/10000000000 : ℝ)|^9 ≤ (892321394819/3125000000000 : ℝ)^7
        have hw : |(3772534509/10000000000 : ℝ)|=(3772534509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3644986379/10000000000 : ℝ)*x 0 + (5236569129/10000000000 : ℝ)*x 1 + (3833847181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3644986379/10000000000 : ℝ)^9 ≤ (6829771568651/25000000000000 : ℝ)^7 := by
    have hnat : (3644986379 : ℕ)^9*25000000000000^7 ≤ 6829771568651^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3644986379 10000000000 6829771568651 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236569129/10000000000 : ℝ)^9 ≤ (21764290515133/50000000000000 : ℝ)^7 := by
    have hnat : (5236569129 : ℕ)^9*50000000000000^7 ≤ 21764290515133^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236569129 10000000000 21764290515133 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3833847181/10000000000 : ℝ)^9 ≤ (1822020792221/6250000000000 : ℝ)^7 := by
    have hnat : (3833847181 : ℕ)^9*6250000000000^7 ≤ 1822020792221^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3833847181 10000000000 1822020792221 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3644986379/10000000000 : ℝ), (5236569129/10000000000 : ℝ), (3833847181/10000000000 : ℝ)] ![(6829771568651/25000000000000 : ℝ), (21764290515133/50000000000000 : ℝ), (1822020792221/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3644986379/10000000000 : ℝ)|^9 ≤ (6829771568651/25000000000000 : ℝ)^7
        have hw : |(-3644986379/10000000000 : ℝ)|=(3644986379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236569129/10000000000 : ℝ)|^9 ≤ (21764290515133/50000000000000 : ℝ)^7
        have hw : |(5236569129/10000000000 : ℝ)|=(5236569129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3833847181/10000000000 : ℝ)|^9 ≤ (1822020792221/6250000000000 : ℝ)^7
        have hw : |(3833847181/10000000000 : ℝ)|=(3833847181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5669469533/10000000000 : ℝ)*x 0 + (-596365831/10000000000 : ℝ)*x 1 + (1438308737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5669469533/10000000000 : ℝ)^9 ≤ (48208761674581/100000000000000 : ℝ)^7 := by
    have hnat : (5669469533 : ℕ)^9*100000000000000^7 ≤ 48208761674581^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669469533 10000000000 48208761674581 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596365831/10000000000 : ℝ)^9 ≤ (2664767071393/100000000000000 : ℝ)^7 := by
    have hnat : (596365831 : ℕ)^9*100000000000000^7 ≤ 2664767071393^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596365831 10000000000 2664767071393 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1438308737/2500000000 : ℝ)^9 ≤ (6140808905699/12500000000000 : ℝ)^7 := by
    have hnat : (1438308737 : ℕ)^9*12500000000000^7 ≤ 6140808905699^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438308737 2500000000 6140808905699 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5669469533/10000000000 : ℝ), (-596365831/10000000000 : ℝ), (1438308737/2500000000 : ℝ)] ![(48208761674581/100000000000000 : ℝ), (2664767071393/100000000000000 : ℝ), (6140808905699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5669469533/10000000000 : ℝ)|^9 ≤ (48208761674581/100000000000000 : ℝ)^7
        have hw : |(5669469533/10000000000 : ℝ)|=(5669469533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-596365831/10000000000 : ℝ)|^9 ≤ (2664767071393/100000000000000 : ℝ)^7
        have hw : |(-596365831/10000000000 : ℝ)|=(596365831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1438308737/2500000000 : ℝ)|^9 ≤ (6140808905699/12500000000000 : ℝ)^7
        have hw : |(1438308737/2500000000 : ℝ)|=(1438308737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3025284389/10000000000 : ℝ)*x 0 + (49461857/78125000 : ℝ)*x 1 + (-1591018021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3025284389/10000000000 : ℝ)^9 ≤ (21498773977933/100000000000000 : ℝ)^7 := by
    have hnat : (3025284389 : ℕ)^9*100000000000000^7 ≤ 21498773977933^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3025284389 10000000000 21498773977933 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49461857/78125000 : ℝ)^9 ≤ (11111955498311/20000000000000 : ℝ)^7 := by
    have hnat : (49461857 : ℕ)^9*20000000000000^7 ≤ 11111955498311^7*78125000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49461857 78125000 11111955498311 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1591018021/5000000000 : ℝ)^9 ≤ (11470724260411/50000000000000 : ℝ)^7 := by
    have hnat : (1591018021 : ℕ)^9*50000000000000^7 ≤ 11470724260411^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591018021 5000000000 11470724260411 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3025284389/10000000000 : ℝ), (49461857/78125000 : ℝ), (-1591018021/5000000000 : ℝ)] ![(21498773977933/100000000000000 : ℝ), (11111955498311/20000000000000 : ℝ), (11470724260411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3025284389/10000000000 : ℝ)|^9 ≤ (21498773977933/100000000000000 : ℝ)^7
        have hw : |(3025284389/10000000000 : ℝ)|=(3025284389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49461857/78125000 : ℝ)|^9 ≤ (11111955498311/20000000000000 : ℝ)^7
        have hw : |(49461857/78125000 : ℝ)|=(49461857/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1591018021/5000000000 : ℝ)|^9 ≤ (11470724260411/50000000000000 : ℝ)^7
        have hw : |(-1591018021/5000000000 : ℝ)|=(1591018021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (234574191/625000000 : ℝ)*x 0 + (1290370261/2500000000 : ℝ)*x 1 + (1904319867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234574191/625000000 : ℝ)^9 ≤ (28366141816579/100000000000000 : ℝ)^7 := by
    have hnat : (234574191 : ℕ)^9*100000000000000^7 ≤ 28366141816579^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234574191 625000000 28366141816579 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290370261/2500000000 : ℝ)^9 ≤ (8545546803533/20000000000000 : ℝ)^7 := by
    have hnat : (1290370261 : ℕ)^9*20000000000000^7 ≤ 8545546803533^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290370261 2500000000 8545546803533 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904319867/5000000000 : ℝ)^9 ≤ (28906124149561/100000000000000 : ℝ)^7 := by
    have hnat : (1904319867 : ℕ)^9*100000000000000^7 ≤ 28906124149561^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904319867 5000000000 28906124149561 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(234574191/625000000 : ℝ), (1290370261/2500000000 : ℝ), (1904319867/5000000000 : ℝ)] ![(28366141816579/100000000000000 : ℝ), (8545546803533/20000000000000 : ℝ), (28906124149561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(234574191/625000000 : ℝ)|^9 ≤ (28366141816579/100000000000000 : ℝ)^7
        have hw : |(234574191/625000000 : ℝ)|=(234574191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1290370261/2500000000 : ℝ)|^9 ≤ (8545546803533/20000000000000 : ℝ)^7
        have hw : |(1290370261/2500000000 : ℝ)|=(1290370261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1904319867/5000000000 : ℝ)|^9 ≤ (28906124149561/100000000000000 : ℝ)^7
        have hw : |(1904319867/5000000000 : ℝ)|=(1904319867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-900277367/2500000000 : ℝ)*x 0 + (249605109/500000000 : ℝ)*x 1 + (4139055659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900277367/2500000000 : ℝ)^9 ≤ (26897000089297/100000000000000 : ℝ)^7 := by
    have hnat : (900277367 : ℕ)^9*100000000000000^7 ≤ 26897000089297^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900277367 2500000000 26897000089297 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249605109/500000000 : ℝ)^9 ≤ (20466743481499/50000000000000 : ℝ)^7 := by
    have hnat : (249605109 : ℕ)^9*50000000000000^7 ≤ 20466743481499^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249605109 500000000 20466743481499 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4139055659/10000000000 : ℝ)^9 ≤ (128678051751/400000000000 : ℝ)^7 := by
    have hnat : (4139055659 : ℕ)^9*400000000000^7 ≤ 128678051751^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139055659 10000000000 128678051751 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-900277367/2500000000 : ℝ), (249605109/500000000 : ℝ), (4139055659/10000000000 : ℝ)] ![(26897000089297/100000000000000 : ℝ), (20466743481499/50000000000000 : ℝ), (128678051751/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-900277367/2500000000 : ℝ)|^9 ≤ (26897000089297/100000000000000 : ℝ)^7
        have hw : |(-900277367/2500000000 : ℝ)|=(900277367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249605109/500000000 : ℝ)|^9 ≤ (20466743481499/50000000000000 : ℝ)^7
        have hw : |(249605109/500000000 : ℝ)|=(249605109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4139055659/10000000000 : ℝ)|^9 ≤ (128678051751/400000000000 : ℝ)^7
        have hw : |(4139055659/10000000000 : ℝ)|=(4139055659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1268192197/2000000000 : ℝ)*x 0 + (-1161689163/10000000000 : ℝ)*x 1 + (4716282649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1268192197/2000000000 : ℝ)^9 ≤ (5567086397773/10000000000000 : ℝ)^7 := by
    have hnat : (1268192197 : ℕ)^9*10000000000000^7 ≤ 5567086397773^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268192197 2000000000 5567086397773 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161689163/10000000000 : ℝ)^9 ≤ (6280189918973/100000000000000 : ℝ)^7 := by
    have hnat : (1161689163 : ℕ)^9*100000000000000^7 ≤ 6280189918973^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161689163 10000000000 6280189918973 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4716282649/10000000000 : ℝ)^9 ≤ (38048946079699/100000000000000 : ℝ)^7 := by
    have hnat : (4716282649 : ℕ)^9*100000000000000^7 ≤ 38048946079699^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4716282649 10000000000 38048946079699 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1268192197/2000000000 : ℝ), (-1161689163/10000000000 : ℝ), (4716282649/10000000000 : ℝ)] ![(5567086397773/10000000000000 : ℝ), (6280189918973/100000000000000 : ℝ), (38048946079699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1268192197/2000000000 : ℝ)|^9 ≤ (5567086397773/10000000000000 : ℝ)^7
        have hw : |(1268192197/2000000000 : ℝ)|=(1268192197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1161689163/10000000000 : ℝ)|^9 ≤ (6280189918973/100000000000000 : ℝ)^7
        have hw : |(-1161689163/10000000000 : ℝ)|=(1161689163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4716282649/10000000000 : ℝ)|^9 ≤ (38048946079699/100000000000000 : ℝ)^7
        have hw : |(4716282649/10000000000 : ℝ)|=(4716282649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3116878557/10000000000 : ℝ)*x 0 + (2932029521/5000000000 : ℝ)*x 1 + (-455560671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3116878557/10000000000 : ℝ)^9 ≤ (22339241270547/100000000000000 : ℝ)^7 := by
    have hnat : (3116878557 : ℕ)^9*100000000000000^7 ≤ 22339241270547^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116878557 10000000000 22339241270547 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2932029521/5000000000 : ℝ)^9 ≤ (50346500283109/100000000000000 : ℝ)^7 := by
    have hnat : (2932029521 : ℕ)^9*100000000000000^7 ≤ 50346500283109^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2932029521 5000000000 50346500283109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455560671/1250000000 : ℝ)^9 ≤ (5462851685601/20000000000000 : ℝ)^7 := by
    have hnat : (455560671 : ℕ)^9*20000000000000^7 ≤ 5462851685601^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455560671 1250000000 5462851685601 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3116878557/10000000000 : ℝ), (2932029521/5000000000 : ℝ), (-455560671/1250000000 : ℝ)] ![(22339241270547/100000000000000 : ℝ), (50346500283109/100000000000000 : ℝ), (5462851685601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3116878557/10000000000 : ℝ)|^9 ≤ (22339241270547/100000000000000 : ℝ)^7
        have hw : |(3116878557/10000000000 : ℝ)|=(3116878557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2932029521/5000000000 : ℝ)|^9 ≤ (50346500283109/100000000000000 : ℝ)^7
        have hw : |(2932029521/5000000000 : ℝ)|=(2932029521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455560671/1250000000 : ℝ)|^9 ≤ (5462851685601/20000000000000 : ℝ)^7
        have hw : |(-455560671/1250000000 : ℝ)|=(455560671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3160624973/10000000000 : ℝ)*x 0 + (5125708571/10000000000 : ℝ)*x 1 + (2205369361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3160624973/10000000000 : ℝ)^9 ≤ (11371583960253/50000000000000 : ℝ)^7 := by
    have hnat : (3160624973 : ℕ)^9*50000000000000^7 ≤ 11371583960253^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3160624973 10000000000 11371583960253 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125708571/10000000000 : ℝ)^9 ≤ (42347371213197/100000000000000 : ℝ)^7 := by
    have hnat : (5125708571 : ℕ)^9*100000000000000^7 ≤ 42347371213197^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125708571 10000000000 42347371213197 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205369361/5000000000 : ℝ)^9 ≤ (34909460853843/100000000000000 : ℝ)^7 := by
    have hnat : (2205369361 : ℕ)^9*100000000000000^7 ≤ 34909460853843^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205369361 5000000000 34909460853843 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3160624973/10000000000 : ℝ), (5125708571/10000000000 : ℝ), (2205369361/5000000000 : ℝ)] ![(11371583960253/50000000000000 : ℝ), (42347371213197/100000000000000 : ℝ), (34909460853843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3160624973/10000000000 : ℝ)|^9 ≤ (11371583960253/50000000000000 : ℝ)^7
        have hw : |(3160624973/10000000000 : ℝ)|=(3160624973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125708571/10000000000 : ℝ)|^9 ≤ (42347371213197/100000000000000 : ℝ)^7
        have hw : |(5125708571/10000000000 : ℝ)|=(5125708571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205369361/5000000000 : ℝ)|^9 ≤ (34909460853843/100000000000000 : ℝ)^7
        have hw : |(2205369361/5000000000 : ℝ)|=(2205369361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3131430399/10000000000 : ℝ)*x 0 + (553436189/1000000000 : ℝ)*x 1 + (4000320329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3131430399/10000000000 : ℝ)^9 ≤ (11236712555421/50000000000000 : ℝ)^7 := by
    have hnat : (3131430399 : ℕ)^9*50000000000000^7 ≤ 11236712555421^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3131430399 10000000000 11236712555421 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553436189/1000000000 : ℝ)^9 ≤ (11684181443661/25000000000000 : ℝ)^7 := by
    have hnat : (553436189 : ℕ)^9*25000000000000^7 ≤ 11684181443661^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553436189 1000000000 11684181443661 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4000320329/10000000000 : ℝ)^9 ≤ (15394924549041/50000000000000 : ℝ)^7 := by
    have hnat : (4000320329 : ℕ)^9*50000000000000^7 ≤ 15394924549041^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000320329 10000000000 15394924549041 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3131430399/10000000000 : ℝ), (553436189/1000000000 : ℝ), (4000320329/10000000000 : ℝ)] ![(11236712555421/50000000000000 : ℝ), (11684181443661/25000000000000 : ℝ), (15394924549041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3131430399/10000000000 : ℝ)|^9 ≤ (11236712555421/50000000000000 : ℝ)^7
        have hw : |(-3131430399/10000000000 : ℝ)|=(3131430399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553436189/1000000000 : ℝ)|^9 ≤ (11684181443661/25000000000000 : ℝ)^7
        have hw : |(553436189/1000000000 : ℝ)|=(553436189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4000320329/10000000000 : ℝ)|^9 ≤ (15394924549041/50000000000000 : ℝ)^7
        have hw : |(4000320329/10000000000 : ℝ)|=(4000320329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6462361719/10000000000 : ℝ)*x 0 + (-35112829/500000000 : ℝ)*x 1 + (243578029/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6462361719/10000000000 : ℝ)^9 ≤ (57044967680441/100000000000000 : ℝ)^7 := by
    have hnat : (6462361719 : ℕ)^9*100000000000000^7 ≤ 57044967680441^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6462361719 10000000000 57044967680441 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35112829/500000000 : ℝ)^9 ≤ (410991846791/12500000000000 : ℝ)^7 := by
    have hnat : (35112829 : ℕ)^9*12500000000000^7 ≤ 410991846791^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35112829 500000000 410991846791 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243578029/500000000 : ℝ)^9 ≤ (1983354876551/5000000000000 : ℝ)^7 := by
    have hnat : (243578029 : ℕ)^9*5000000000000^7 ≤ 1983354876551^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243578029 500000000 1983354876551 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6462361719/10000000000 : ℝ), (-35112829/500000000 : ℝ), (243578029/500000000 : ℝ)] ![(57044967680441/100000000000000 : ℝ), (410991846791/12500000000000 : ℝ), (1983354876551/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6462361719/10000000000 : ℝ)|^9 ≤ (57044967680441/100000000000000 : ℝ)^7
        have hw : |(6462361719/10000000000 : ℝ)|=(6462361719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35112829/500000000 : ℝ)|^9 ≤ (410991846791/12500000000000 : ℝ)^7
        have hw : |(-35112829/500000000 : ℝ)|=(35112829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243578029/500000000 : ℝ)|^9 ≤ (1983354876551/5000000000000 : ℝ)^7
        have hw : |(243578029/500000000 : ℝ)|=(243578029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2776574801/10000000000 : ℝ)*x 0 + (6225227051/10000000000 : ℝ)*x 1 + (-886750399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2776574801/10000000000 : ℝ)^9 ≤ (1203350311173/6250000000000 : ℝ)^7 := by
    have hnat : (2776574801 : ℕ)^9*6250000000000^7 ≤ 1203350311173^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776574801 10000000000 1203350311173 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6225227051/10000000000 : ℝ)^9 ≤ (10873575904471/20000000000000 : ℝ)^7 := by
    have hnat : (6225227051 : ℕ)^9*20000000000000^7 ≤ 10873575904471^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6225227051 10000000000 10873575904471 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886750399/2500000000 : ℝ)^9 ≤ (26378515472179/100000000000000 : ℝ)^7 := by
    have hnat : (886750399 : ℕ)^9*100000000000000^7 ≤ 26378515472179^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886750399 2500000000 26378515472179 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2776574801/10000000000 : ℝ), (6225227051/10000000000 : ℝ), (-886750399/2500000000 : ℝ)] ![(1203350311173/6250000000000 : ℝ), (10873575904471/20000000000000 : ℝ), (26378515472179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2776574801/10000000000 : ℝ)|^9 ≤ (1203350311173/6250000000000 : ℝ)^7
        have hw : |(2776574801/10000000000 : ℝ)|=(2776574801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6225227051/10000000000 : ℝ)|^9 ≤ (10873575904471/20000000000000 : ℝ)^7
        have hw : |(6225227051/10000000000 : ℝ)|=(6225227051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-886750399/2500000000 : ℝ)|^9 ≤ (26378515472179/100000000000000 : ℝ)^7
        have hw : |(-886750399/2500000000 : ℝ)|=(886750399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310031_s2_s2_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2350095677/5000000000 : ℝ)*x 0 + (4495658177/10000000000 : ℝ)*x 1 + (3543173211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2350095677/5000000000 : ℝ)^9 ≤ (9470529767001/25000000000000 : ℝ)^7 := by
    have hnat : (2350095677 : ℕ)^9*25000000000000^7 ≤ 9470529767001^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350095677 5000000000 9470529767001 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495658177/10000000000 : ℝ)^9 ≤ (715519310579/2000000000000 : ℝ)^7 := by
    have hnat : (4495658177 : ℕ)^9*2000000000000^7 ≤ 715519310579^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495658177 10000000000 715519310579 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3543173211/10000000000 : ℝ)^9 ≤ (13170957695193/50000000000000 : ℝ)^7 := by
    have hnat : (3543173211 : ℕ)^9*50000000000000^7 ≤ 13170957695193^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3543173211 10000000000 13170957695193 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2350095677/5000000000 : ℝ), (4495658177/10000000000 : ℝ), (3543173211/10000000000 : ℝ)] ![(9470529767001/25000000000000 : ℝ), (715519310579/2000000000000 : ℝ), (13170957695193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2350095677/5000000000 : ℝ)|^9 ≤ (9470529767001/25000000000000 : ℝ)^7
        have hw : |(2350095677/5000000000 : ℝ)|=(2350095677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495658177/10000000000 : ℝ)|^9 ≤ (715519310579/2000000000000 : ℝ)^7
        have hw : |(4495658177/10000000000 : ℝ)|=(4495658177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3543173211/10000000000 : ℝ)|^9 ≤ (13170957695193/50000000000000 : ℝ)^7
        have hw : |(3543173211/10000000000 : ℝ)|=(3543173211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310031_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((11303/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11303/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1257/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1257/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31727/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31727/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2589/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2589/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23701/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23701/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (11303/20000 : ℝ) ^ (35/8 : ℝ) ≤ (1647199959332999143/20000000000000000000 : ℝ) := by
    have hpowers : (11303/20000 : ℝ)^35 ≤ (1647199959332999143/20000000000000000000 : ℝ)^8 := by
      have hnat : (11303 : ℕ)^35*20000000000000000000^8 ≤ 1647199959332999143^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11303 20000 1647199959332999143 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11303/20000 : ℝ)) (X := (1647199959332999143/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (21647199959332999143/20000000000000000000 : ℝ) ≤ (10182546362209281/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (21647199959332999143/20000000000000000000 : ℝ)^8 ≤ (10182546362209281/10000000000000000 : ℝ)^35 := by
      have hnat : (21647199959332999143 : ℕ)^8*10000000000000000^35 ≤ 10182546362209281^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21647199959332999143 20000000000000000000 10182546362209281 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10182546362209281/10000000000000000 : ℝ)) (X := (21647199959332999143/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (11647199959332999143/10000000000000000000 : ℝ) ≤ (5177336042333553/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (11647199959332999143/10000000000000000000 : ℝ)^8 ≤ (5177336042333553/5000000000000000 : ℝ)^35 := by
      have hnat : (11647199959332999143 : ℕ)^8*5000000000000000^35 ≤ 5177336042333553^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11647199959332999143 10000000000000000000 5177336042333553 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5177336042333553/5000000000000000 : ℝ)) (X := (11647199959332999143/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(182546362209281/5651500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6885028898313/226060000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (11303/20000 : ℝ)) (alpha := (182546362209281/5651500000000000 : ℝ)) (beta := (6885028898313/226060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11303/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(182546362209281/5651500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6885028898313/226060000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (1257/6250 : ℝ) ^ (35/8 : ℝ) ≤ (89663722256534493/100000000000000000000 : ℝ) := by
    have hpowers : (1257/6250 : ℝ)^35 ≤ (89663722256534493/100000000000000000000 : ℝ)^8 := by
      have hnat : (1257 : ℕ)^35*100000000000000000000^8 ≤ 89663722256534493^8*6250^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1257 6250 89663722256534493 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1257/6250 : ℝ)) (X := (89663722256534493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (100089663722256534493/100000000000000000000 : ℝ) ≤ (5001024374043929/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100089663722256534493/100000000000000000000 : ℝ)^8 ≤ (5001024374043929/5000000000000000 : ℝ)^35 := by
      have hnat : (100089663722256534493 : ℕ)^8*5000000000000000^35 ≤ 5001024374043929^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100089663722256534493 100000000000000000000 5001024374043929 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001024374043929/5000000000000000 : ℝ)) (X := (100089663722256534493/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (50089663722256534493/50000000000000000000 : ℝ) ≤ (5002048040416133/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50089663722256534493/50000000000000000000 : ℝ)^8 ≤ (5002048040416133/5000000000000000 : ℝ)^35 := by
      have hnat : (50089663722256534493 : ℕ)^8*5000000000000000^35 ≤ 5002048040416133^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50089663722256534493 50000000000000000000 5002048040416133 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002048040416133/5000000000000000 : ℝ)) (X := (50089663722256534493/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(341458014643/335200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(85305531017/83800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1257/6250 : ℝ)) (alpha := (341458014643/335200000000000 : ℝ)) (beta := (85305531017/83800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1257/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(341458014643/335200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(85305531017/83800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (31727/50000 : ℝ) ^ (35/8 : ℝ) ≤ (2733934712956169629/20000000000000000000 : ℝ) := by
    have hpowers : (31727/50000 : ℝ)^35 ≤ (2733934712956169629/20000000000000000000 : ℝ)^8 := by
      have hnat : (31727 : ℕ)^35*20000000000000000000^8 ≤ 2733934712956169629^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31727 50000 2733934712956169629 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31727/50000 : ℝ)) (X := (2733934712956169629/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (22733934712956169629/20000000000000000000 : ℝ) ≤ (32178721890073/31250000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (22733934712956169629/20000000000000000000 : ℝ)^8 ≤ (32178721890073/31250000000000 : ℝ)^35 := by
      have hnat : (22733934712956169629 : ℕ)^8*31250000000000^35 ≤ 32178721890073^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22733934712956169629 20000000000000000000 32178721890073 31250000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (32178721890073/31250000000000 : ℝ)) (X := (22733934712956169629/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (12733934712956169629/10000000000000000000 : ℝ) ≤ (5283983588661447/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (12733934712956169629/10000000000000000000 : ℝ)^8 ≤ (5283983588661447/5000000000000000 : ℝ)^35 := by
      have hnat : (12733934712956169629 : ℕ)^8*5000000000000000^35 ≤ 5283983588661447^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12733934712956169629 10000000000000000000 5283983588661447 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5283983588661447/5000000000000000 : ℝ)) (X := (12733934712956169629/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(928721890073/19829375000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(135388086249767/3172700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (31727/50000 : ℝ)) (alpha := (928721890073/19829375000000 : ℝ)) (beta := (135388086249767/3172700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31727/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(928721890073/19829375000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(135388086249767/3172700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3538564871/10000000000 : ℝ)*X 0 0+(5341043077/10000000000 : ℝ)*X 0 1+(3823767191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5740248447/10000000000 : ℝ)*X 1 0+(-1208101051/10000000000 : ℝ)*X 1 1+(5318992733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((3341981461/10000000000 : ℝ)*X 2 0+(22809981/40000000 : ℝ)*X 2 1+(-3611339493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2035656603/5000000000 : ℝ)*X 0 0+(2449354961/5000000000 : ℝ)*X 0 1+(3772534509/10000000000 : ℝ)*X 0 2+(2035656603/5000000000 : ℝ)*X 1 0+(2449354961/5000000000 : ℝ)*X 1 1+(3772534509/10000000000 : ℝ)*X 1 2+(2035656603/5000000000 : ℝ)*X 2 0+(2449354961/5000000000 : ℝ)*X 2 1+(3772534509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-3644986379/10000000000 : ℝ)*X 0 0+(5236569129/10000000000 : ℝ)*X 0 1+(3833847181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5669469533/10000000000 : ℝ)*X 1 0+(-596365831/10000000000 : ℝ)*X 1 1+(1438308737/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3025284389/10000000000 : ℝ)*X 2 0+(49461857/78125000 : ℝ)*X 2 1+(-1591018021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((234574191/625000000 : ℝ)*X 0 0+(1290370261/2500000000 : ℝ)*X 0 1+(1904319867/5000000000 : ℝ)*X 0 2+(234574191/625000000 : ℝ)*X 1 0+(1290370261/2500000000 : ℝ)*X 1 1+(1904319867/5000000000 : ℝ)*X 1 2+(234574191/625000000 : ℝ)*X 2 0+(1290370261/2500000000 : ℝ)*X 2 1+(1904319867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-900277367/2500000000 : ℝ)*X 0 0+(249605109/500000000 : ℝ)*X 0 1+(4139055659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1268192197/2000000000 : ℝ)*X 1 0+(-1161689163/10000000000 : ℝ)*X 1 1+(4716282649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3116878557/10000000000 : ℝ)*X 2 0+(2932029521/5000000000 : ℝ)*X 2 1+(-455560671/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((3160624973/10000000000 : ℝ)*X 0 0+(5125708571/10000000000 : ℝ)*X 0 1+(2205369361/5000000000 : ℝ)*X 0 2+(3160624973/10000000000 : ℝ)*X 1 0+(5125708571/10000000000 : ℝ)*X 1 1+(2205369361/5000000000 : ℝ)*X 1 2+(3160624973/10000000000 : ℝ)*X 2 0+(5125708571/10000000000 : ℝ)*X 2 1+(2205369361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-3131430399/10000000000 : ℝ)*X 0 0+(553436189/1000000000 : ℝ)*X 0 1+(4000320329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6462361719/10000000000 : ℝ)*X 1 0+(-35112829/500000000 : ℝ)*X 1 1+(243578029/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2776574801/10000000000 : ℝ)*X 2 0+(6225227051/10000000000 : ℝ)*X 2 1+(-886750399/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((2350095677/5000000000 : ℝ)*X 0 0+(4495658177/10000000000 : ℝ)*X 0 1+(3543173211/10000000000 : ℝ)*X 0 2+(2350095677/5000000000 : ℝ)*X 1 0+(4495658177/10000000000 : ℝ)*X 1 1+(3543173211/10000000000 : ℝ)*X 1 2+(2350095677/5000000000 : ℝ)*X 2 0+(4495658177/10000000000 : ℝ)*X 2 1+(3543173211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310031_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((19417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1291124065772639754163190953809/75128853869500000000000000000000000 : ℝ) := by norm_num
    linear_combination (252883145451/500000000000 : ℝ)*(base49) + (1964684006513/1000000000000 : ℝ)*(base50) + (1941/2500000000 : ℝ)*(base60) + (6186962268987/1000000000000 : ℝ)*(major_s2_0) + (6186962268987/1000000000000 : ℝ)*(major_s2_1) + (6186962268987/1000000000000 : ℝ)*(major_s2_2) + (610519157/1000000000000 : ℝ)*(sp_s2_0) + (78628899/1000000000000 : ℝ)*(sp_s2_1) + (4274577854481/500000000000 : ℝ)*(sp_s2_7) + (4274920724129/500000000000 : ℝ)*(sp_s2_8) + (8549920077157/1000000000000 : ℝ)*(sp_s2_9) + (764778026047/200000000000 : ℝ)*(sp_s2_12) + (153849037/1000000000000 : ℝ)*(sp_s2_13) + (108602087/1000000000000 : ℝ)*(sp_s2_19) + (3823998732323/1000000000000 : ℝ)*(f.failure) + (8549920077157/1000000000000 : ℝ)*(f.sum) + (4459964742897852687/10634890400000000000000000000000 : ℝ)*base62 + (3108996690444749/3172700000000000000000000000 : ℝ)*base65 + (68471712079299/83800000000000000000000000 : ℝ)*base67 + (16151490395941/31727000000000000000000000 : ℝ)*base69 + (6281056914989456963/22413142562500000000000000000000 : ℝ)*base71 + (109874981904801/226060000000000000000000000 : ℝ)*base73 + (14219907431679/335200000000000000000000000 : ℝ)*base75 + (2991483318089997/5651500000000000000000000000 : ℝ)*base77 + (228010008997463527/947191400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (35139/100000000000000000 : ℝ)*base87 + (35139/100000000000000000 : ℝ)*base89 + (35139/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2589/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2589/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (231564264227786246560768679091/15025770773900000000000000000000000 : ℝ) := by norm_num
    linear_combination (490026847587/1000000000000 : ℝ)*(base40) + (72252669093/100000000000 : ℝ)*(base50) + (7155722553/62500000000 : ℝ)*(base60) + (1154821157071/250000000000 : ℝ)*(major_s2_0) + (1154821157071/250000000000 : ℝ)*(major_s2_1) + (1154821157071/250000000000 : ℝ)*(major_s2_2) + (178518323/1000000000000 : ℝ)*(sp_s2_1) + (654711667/1000000000000 : ℝ)*(sp_s2_2) + (23042773/500000000000 : ℝ)*(sp_s2_9) + (1595876431243/250000000000 : ℝ)*(sp_s2_13) + (6383228204593/1000000000000 : ℝ)*(sp_s2_14) + (3191402463879/500000000000 : ℝ)*(sp_s2_15) + (178441149659/62500000000 : ℝ)*(sp_s2_19) + (12375257/125000000000 : ℝ)*(sp_s2_21) + (178441149659/62500000000 : ℝ)*(f.failure) + (1595876431243/250000000000 : ℝ)*(f.sum) + (1293394361917638669/2658722600000000000000000000000 : ℝ)*base63 + (213236985981463/793175000000000000000000000 : ℝ)*base64 + (7541208554187/20950000000000000000000000 : ℝ)*base67 + (22416566374319/158635000000000000000000000 : ℝ)*base69 + (18800700491026249959/22413142562500000000000000000000 : ℝ)*base70 + (20326177481327/56515000000000000000000000 : ℝ)*base73 + (62219179645727/83800000000000000000000000 : ℝ)*base75 + (950093585859/22076171875000000000000000 : ℝ)*base77 + (42457085242060103/118398925000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (3587/6250000000000000 : ℝ)*base87 + (3587/6250000000000000 : ℝ)*base89 + (3587/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23701/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23701/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (86462603634420679927795045149/15025770773900000000000000000000000 : ℝ) := by norm_num
    linear_combination (387082138007/500000000000 : ℝ)*(base40) + (187195150011/200000000000 : ℝ)*(base49) + (2375437265003/1000000000000 : ℝ)*(base50) + (1828540352073/250000000000 : ℝ)*(major_s2_0) + (1828540352073/250000000000 : ℝ)*(major_s2_1) + (1828540352073/250000000000 : ℝ)*(major_s2_2) + (25871539/1000000000000 : ℝ)*(sp_s2_6) + (24332979/250000000000 : ℝ)*(sp_s2_9) + (1495667/25000000000 : ℝ)*(sp_s2_14) + (6862637/100000000000 : ℝ)*(sp_s2_15) + (2021526002113/200000000000 : ℝ)*(sp_s2_20) + (2021514036777/200000000000 : ℝ)*(sp_s2_21) + (252686601307/25000000000 : ℝ)*(sp_s2_22) + (4520665016381/1000000000000 : ℝ)*(sp_s2_25) + (56508636099/12500000000 : ℝ)*(f.failure) + (2021526002113/200000000000 : ℝ)*(f.sum) + (821665399914610647/2658722600000000000000000000000 : ℝ)*base63 + (143620185943407/1586350000000000000000000000 : ℝ)*base65 + (698316113669/5237500000000000000000000 : ℝ)*base67 + (5457534970267/63454000000000000000000000 : ℝ)*base69 + (25668268940877684257/89652570250000000000000000000000 : ℝ)*base71 + (8937481924247/28257500000000000000000000 : ℝ)*base72 + (21687551090301/83800000000000000000000000 : ℝ)*base75 + (238768625034799/2825750000000000000000000000 : ℝ)*base76 + (53342208499260217/236797850000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (507/1250000000000000 : ℝ)*base87 + (507/1250000000000000 : ℝ)*base89 + (507/1250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((11303/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11303/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1257/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1257/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31727/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31727/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19417/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19417/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2589/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2589/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23701/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23701/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310031_s2 p hpa hpb X hX hprev1

#print axioms solution
