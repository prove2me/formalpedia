-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:54.002284+00:00
-- url     : https://prove2.me/submissions/f03dca82-17c1-4e2c-b769-c42ad0b11bd0

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
theorem collision_support_c315055_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-731759467/5000000000 : ℝ)*x 0 + (2905889331/5000000000 : ℝ)*x 1 + (4941411657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (731759467/5000000000 : ℝ)^19 ≤ (1753347101911/20000000000000 : ℝ)^15 := by
    have hnat : (731759467 : ℕ)^19*20000000000000^15 ≤ 1753347101911^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731759467 5000000000 1753347101911 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2905889331/5000000000 : ℝ)^19 ≤ (50287280555099/100000000000000 : ℝ)^15 := by
    have hnat : (2905889331 : ℕ)^19*100000000000000^15 ≤ 50287280555099^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905889331 5000000000 50287280555099 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4941411657/10000000000 : ℝ)^19 ≤ (20472991959111/50000000000000 : ℝ)^15 := by
    have hnat : (4941411657 : ℕ)^19*50000000000000^15 ≤ 20472991959111^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4941411657 10000000000 20472991959111 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-731759467/5000000000 : ℝ), (2905889331/5000000000 : ℝ), (4941411657/10000000000 : ℝ)] ![(1753347101911/20000000000000 : ℝ), (50287280555099/100000000000000 : ℝ), (20472991959111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-731759467/5000000000 : ℝ)|^19 ≤ (1753347101911/20000000000000 : ℝ)^15
        have hw : |(-731759467/5000000000 : ℝ)|=(731759467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2905889331/5000000000 : ℝ)|^19 ≤ (50287280555099/100000000000000 : ℝ)^15
        have hw : |(2905889331/5000000000 : ℝ)|=(2905889331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4941411657/10000000000 : ℝ)|^19 ≤ (20472991959111/50000000000000 : ℝ)^15
        have hw : |(4941411657/10000000000 : ℝ)|=(4941411657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (484631203/1000000000 : ℝ)*x 0 + (-441620073/10000000000 : ℝ)*x 1 + (1629021401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (484631203/1000000000 : ℝ)^19 ≤ (39950394495973/100000000000000 : ℝ)^15 := by
    have hnat : (484631203 : ℕ)^19*100000000000000^15 ≤ 39950394495973^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484631203 1000000000 39950394495973 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441620073/10000000000 : ℝ)^19 ≤ (1921889820897/100000000000000 : ℝ)^15 := by
    have hnat : (441620073 : ℕ)^19*100000000000000^15 ≤ 1921889820897^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441620073 10000000000 1921889820897 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1629021401/2500000000 : ℝ)^19 ≤ (58127715661051/100000000000000 : ℝ)^15 := by
    have hnat : (1629021401 : ℕ)^19*100000000000000^15 ≤ 58127715661051^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629021401 2500000000 58127715661051 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(484631203/1000000000 : ℝ), (-441620073/10000000000 : ℝ), (1629021401/2500000000 : ℝ)] ![(39950394495973/100000000000000 : ℝ), (1921889820897/100000000000000 : ℝ), (58127715661051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(484631203/1000000000 : ℝ)|^19 ≤ (39950394495973/100000000000000 : ℝ)^15
        have hw : |(484631203/1000000000 : ℝ)|=(484631203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441620073/10000000000 : ℝ)|^19 ≤ (1921889820897/100000000000000 : ℝ)^15
        have hw : |(-441620073/10000000000 : ℝ)|=(441620073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1629021401/2500000000 : ℝ)|^19 ≤ (58127715661051/100000000000000 : ℝ)^15
        have hw : |(1629021401/2500000000 : ℝ)|=(1629021401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2413311291/5000000000 : ℝ)*x 0 + (5947581503/10000000000 : ℝ)*x 1 + (-712452797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2413311291/5000000000 : ℝ)^19 ≤ (39744914274257/100000000000000 : ℝ)^15 := by
    have hnat : (2413311291 : ℕ)^19*100000000000000^15 ≤ 39744914274257^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413311291 5000000000 39744914274257 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5947581503/10000000000 : ℝ)^19 ≤ (51780293690381/100000000000000 : ℝ)^15 := by
    have hnat : (5947581503 : ℕ)^19*100000000000000^15 ≤ 51780293690381^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947581503 10000000000 51780293690381 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712452797/5000000000 : ℝ)^19 ≤ (4237396011971/50000000000000 : ℝ)^15 := by
    have hnat : (712452797 : ℕ)^19*50000000000000^15 ≤ 4237396011971^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712452797 5000000000 4237396011971 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2413311291/5000000000 : ℝ), (5947581503/10000000000 : ℝ), (-712452797/5000000000 : ℝ)] ![(39744914274257/100000000000000 : ℝ), (51780293690381/100000000000000 : ℝ), (4237396011971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2413311291/5000000000 : ℝ)|^19 ≤ (39744914274257/100000000000000 : ℝ)^15
        have hw : |(2413311291/5000000000 : ℝ)|=(2413311291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5947581503/10000000000 : ℝ)|^19 ≤ (51780293690381/100000000000000 : ℝ)^15
        have hw : |(5947581503/10000000000 : ℝ)|=(5947581503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-712452797/5000000000 : ℝ)|^19 ≤ (4237396011971/50000000000000 : ℝ)^15
        have hw : |(-712452797/5000000000 : ℝ)|=(712452797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (259363243/400000000 : ℝ)*x 0 + (376478137/1000000000 : ℝ)*x 1 + (12650681/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259363243/400000000 : ℝ)^19 ≤ (2888315896999/5000000000000 : ℝ)^15 := by
    have hnat : (259363243 : ℕ)^19*5000000000000^15 ≤ 2888315896999^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259363243 400000000 2888315896999 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376478137/1000000000 : ℝ)^19 ≤ (29013738799447/100000000000000 : ℝ)^15 := by
    have hnat : (376478137 : ℕ)^19*100000000000000^15 ≤ 29013738799447^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376478137 1000000000 29013738799447 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12650681/62500000 : ℝ)^19 ≤ (3304985811/25000000000 : ℝ)^15 := by
    have hnat : (12650681 : ℕ)^19*25000000000^15 ≤ 3304985811^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12650681 62500000 3304985811 25000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259363243/400000000 : ℝ), (376478137/1000000000 : ℝ), (12650681/62500000 : ℝ)] ![(2888315896999/5000000000000 : ℝ), (29013738799447/100000000000000 : ℝ), (3304985811/25000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259363243/400000000 : ℝ)|^19 ≤ (2888315896999/5000000000000 : ℝ)^15
        have hw : |(259363243/400000000 : ℝ)|=(259363243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376478137/1000000000 : ℝ)|^19 ≤ (29013738799447/100000000000000 : ℝ)^15
        have hw : |(376478137/1000000000 : ℝ)|=(376478137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12650681/62500000 : ℝ)|^19 ≤ (3304985811/25000000000 : ℝ)^15
        have hw : |(12650681/62500000 : ℝ)|=(12650681/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-210189599/1250000000 : ℝ)*x 0 + (1889867213/5000000000 : ℝ)*x 1 + (335764293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210189599/1250000000 : ℝ)^19 ≤ (5226266302489/50000000000000 : ℝ)^15 := by
    have hnat : (210189599 : ℕ)^19*50000000000000^15 ≤ 5226266302489^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210189599 1250000000 5226266302489 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889867213/5000000000 : ℝ)^19 ≤ (5831956709677/20000000000000 : ℝ)^15 := by
    have hnat : (1889867213 : ℕ)^19*20000000000000^15 ≤ 5831956709677^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889867213 5000000000 5831956709677 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335764293/500000000 : ℝ)^19 ≤ (60387683835821/100000000000000 : ℝ)^15 := by
    have hnat : (335764293 : ℕ)^19*100000000000000^15 ≤ 60387683835821^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335764293 500000000 60387683835821 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210189599/1250000000 : ℝ), (1889867213/5000000000 : ℝ), (335764293/500000000 : ℝ)] ![(5226266302489/50000000000000 : ℝ), (5831956709677/20000000000000 : ℝ), (60387683835821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210189599/1250000000 : ℝ)|^19 ≤ (5226266302489/50000000000000 : ℝ)^15
        have hw : |(-210189599/1250000000 : ℝ)|=(210189599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1889867213/5000000000 : ℝ)|^19 ≤ (5831956709677/20000000000000 : ℝ)^15
        have hw : |(1889867213/5000000000 : ℝ)|=(1889867213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(335764293/500000000 : ℝ)|^19 ≤ (60387683835821/100000000000000 : ℝ)^15
        have hw : |(335764293/500000000 : ℝ)|=(335764293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (716994577/2000000000 : ℝ)*x 0 + (-5841/50000000 : ℝ)*x 1 + (972148259/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (716994577/2000000000 : ℝ)^19 ≤ (27269809784761/100000000000000 : ℝ)^15 := by
    have hnat : (716994577 : ℕ)^19*100000000000000^15 ≤ 27269809784761^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716994577 2000000000 27269809784761 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5841/50000000 : ℝ)^19 ≤ (1044371767/100000000000000 : ℝ)^15 := by
    have hnat : (5841 : ℕ)^19*100000000000000^15 ≤ 1044371767^15*50000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5841 50000000 1044371767 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (972148259/1250000000 : ℝ)^19 ≤ (72729145826641/100000000000000 : ℝ)^15 := by
    have hnat : (972148259 : ℕ)^19*100000000000000^15 ≤ 72729145826641^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972148259 1250000000 72729145826641 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(716994577/2000000000 : ℝ), (-5841/50000000 : ℝ), (972148259/1250000000 : ℝ)] ![(27269809784761/100000000000000 : ℝ), (1044371767/100000000000000 : ℝ), (72729145826641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(716994577/2000000000 : ℝ)|^19 ≤ (27269809784761/100000000000000 : ℝ)^15
        have hw : |(716994577/2000000000 : ℝ)|=(716994577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5841/50000000 : ℝ)|^19 ≤ (1044371767/100000000000000 : ℝ)^15
        have hw : |(-5841/50000000 : ℝ)|=(5841/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(972148259/1250000000 : ℝ)|^19 ≤ (72729145826641/100000000000000 : ℝ)^15
        have hw : |(972148259/1250000000 : ℝ)|=(972148259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3561912281/10000000000 : ℝ)*x 0 + (7481959037/10000000000 : ℝ)*x 1 + (-370519757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3561912281/10000000000 : ℝ)^19 ≤ (27047808227177/100000000000000 : ℝ)^15 := by
    have hnat : (3561912281 : ℕ)^19*100000000000000^15 ≤ 27047808227177^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3561912281 10000000000 27047808227177 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7481959037/10000000000 : ℝ)^19 ≤ (8656242732587/12500000000000 : ℝ)^15 := by
    have hnat : (7481959037 : ℕ)^19*12500000000000^15 ≤ 8656242732587^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7481959037 10000000000 8656242732587 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370519757/5000000000 : ℝ)^19 ≤ (3702249904073/100000000000000 : ℝ)^15 := by
    have hnat : (370519757 : ℕ)^19*100000000000000^15 ≤ 3702249904073^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370519757 5000000000 3702249904073 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3561912281/10000000000 : ℝ), (7481959037/10000000000 : ℝ), (-370519757/5000000000 : ℝ)] ![(27047808227177/100000000000000 : ℝ), (8656242732587/12500000000000 : ℝ), (3702249904073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3561912281/10000000000 : ℝ)|^19 ≤ (27047808227177/100000000000000 : ℝ)^15
        have hw : |(3561912281/10000000000 : ℝ)|=(3561912281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7481959037/10000000000 : ℝ)|^19 ≤ (8656242732587/12500000000000 : ℝ)^15
        have hw : |(7481959037/10000000000 : ℝ)|=(7481959037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370519757/5000000000 : ℝ)|^19 ≤ (3702249904073/100000000000000 : ℝ)^15
        have hw : |(-370519757/5000000000 : ℝ)|=(370519757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (834780509/2000000000 : ℝ)*x 0 + (6747353041/10000000000 : ℝ)*x 1 + (1110916063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834780509/2000000000 : ℝ)^19 ≤ (33063862476133/100000000000000 : ℝ)^15 := by
    have hnat : (834780509 : ℕ)^19*100000000000000^15 ≤ 33063862476133^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834780509 2000000000 33063862476133 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6747353041/10000000000 : ℝ)^19 ≤ (60753180231421/100000000000000 : ℝ)^15 := by
    have hnat : (6747353041 : ℕ)^19*100000000000000^15 ≤ 60753180231421^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6747353041 10000000000 60753180231421 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110916063/10000000000 : ℝ)^19 ≤ (1236591454819/20000000000000 : ℝ)^15 := by
    have hnat : (1110916063 : ℕ)^19*20000000000000^15 ≤ 1236591454819^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110916063 10000000000 1236591454819 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834780509/2000000000 : ℝ), (6747353041/10000000000 : ℝ), (1110916063/10000000000 : ℝ)] ![(33063862476133/100000000000000 : ℝ), (60753180231421/100000000000000 : ℝ), (1236591454819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834780509/2000000000 : ℝ)|^19 ≤ (33063862476133/100000000000000 : ℝ)^15
        have hw : |(834780509/2000000000 : ℝ)|=(834780509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6747353041/10000000000 : ℝ)|^19 ≤ (60753180231421/100000000000000 : ℝ)^15
        have hw : |(6747353041/10000000000 : ℝ)|=(6747353041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110916063/10000000000 : ℝ)|^19 ≤ (1236591454819/20000000000000 : ℝ)^15
        have hw : |(1110916063/10000000000 : ℝ)|=(1110916063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-58903739/1250000000 : ℝ)*x 0 + (4351267623/10000000000 : ℝ)*x 1 + (1389762671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58903739/1250000000 : ℝ)^19 ≤ (1043273752409/50000000000000 : ℝ)^15 := by
    have hnat : (58903739 : ℕ)^19*50000000000000^15 ≤ 1043273752409^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58903739 1250000000 1043273752409 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4351267623/10000000000 : ℝ)^19 ≤ (34853522256799/100000000000000 : ℝ)^15 := by
    have hnat : (4351267623 : ℕ)^19*100000000000000^15 ≤ 34853522256799^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351267623 10000000000 34853522256799 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389762671/2000000000 : ℝ)^19 ≤ (63059930216551/100000000000000 : ℝ)^15 := by
    have hnat : (1389762671 : ℕ)^19*100000000000000^15 ≤ 63059930216551^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389762671 2000000000 63059930216551 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58903739/1250000000 : ℝ), (4351267623/10000000000 : ℝ), (1389762671/2000000000 : ℝ)] ![(1043273752409/50000000000000 : ℝ), (34853522256799/100000000000000 : ℝ), (63059930216551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58903739/1250000000 : ℝ)|^19 ≤ (1043273752409/50000000000000 : ℝ)^15
        have hw : |(-58903739/1250000000 : ℝ)|=(58903739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4351267623/10000000000 : ℝ)|^19 ≤ (34853522256799/100000000000000 : ℝ)^15
        have hw : |(4351267623/10000000000 : ℝ)|=(4351267623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1389762671/2000000000 : ℝ)|^19 ≤ (63059930216551/100000000000000 : ℝ)^15
        have hw : |(1389762671/2000000000 : ℝ)|=(1389762671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (59676717/200000000 : ℝ)*x 0 + (-627906487/10000000000 : ℝ)*x 1 + (8000592377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59676717/200000000 : ℝ)^19 ≤ (21612992774241/100000000000000 : ℝ)^15 := by
    have hnat : (59676717 : ℕ)^19*100000000000000^15 ≤ 21612992774241^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59676717 200000000 21612992774241 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627906487/10000000000 : ℝ)^19 ≤ (187591711541/6250000000000 : ℝ)^15 := by
    have hnat : (627906487 : ℕ)^19*6250000000000^15 ≤ 187591711541^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627906487 10000000000 187591711541 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8000592377/10000000000 : ℝ)^19 ≤ (75385539832297/100000000000000 : ℝ)^15 := by
    have hnat : (8000592377 : ℕ)^19*100000000000000^15 ≤ 75385539832297^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8000592377 10000000000 75385539832297 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(59676717/200000000 : ℝ), (-627906487/10000000000 : ℝ), (8000592377/10000000000 : ℝ)] ![(21612992774241/100000000000000 : ℝ), (187591711541/6250000000000 : ℝ), (75385539832297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(59676717/200000000 : ℝ)|^19 ≤ (21612992774241/100000000000000 : ℝ)^15
        have hw : |(59676717/200000000 : ℝ)|=(59676717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627906487/10000000000 : ℝ)|^19 ≤ (187591711541/6250000000000 : ℝ)^15
        have hw : |(-627906487/10000000000 : ℝ)|=(627906487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8000592377/10000000000 : ℝ)|^19 ≤ (75385539832297/100000000000000 : ℝ)^15
        have hw : |(8000592377/10000000000 : ℝ)|=(8000592377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6825627323/10000000000 : ℝ)*x 0 + (2254400059/5000000000 : ℝ)*x 1 + (-436412751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6825627323/10000000000 : ℝ)^19 ≤ (30823640385623/50000000000000 : ℝ)^15 := by
    have hnat : (6825627323 : ℕ)^19*50000000000000^15 ≤ 30823640385623^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6825627323 10000000000 30823640385623 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254400059/5000000000 : ℝ)^19 ≤ (18229744530397/50000000000000 : ℝ)^15 := by
    have hnat : (2254400059 : ℕ)^19*50000000000000^15 ≤ 18229744530397^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254400059 5000000000 18229744530397 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436412751/10000000000 : ℝ)^19 ≤ (189323015351/10000000000000 : ℝ)^15 := by
    have hnat : (436412751 : ℕ)^19*10000000000000^15 ≤ 189323015351^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436412751 10000000000 189323015351 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6825627323/10000000000 : ℝ), (2254400059/5000000000 : ℝ), (-436412751/10000000000 : ℝ)] ![(30823640385623/50000000000000 : ℝ), (18229744530397/50000000000000 : ℝ), (189323015351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6825627323/10000000000 : ℝ)|^19 ≤ (30823640385623/50000000000000 : ℝ)^15
        have hw : |(6825627323/10000000000 : ℝ)|=(6825627323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254400059/5000000000 : ℝ)|^19 ≤ (18229744530397/50000000000000 : ℝ)^15
        have hw : |(2254400059/5000000000 : ℝ)|=(2254400059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436412751/10000000000 : ℝ)|^19 ≤ (189323015351/10000000000000 : ℝ)^15
        have hw : |(-436412751/10000000000 : ℝ)|=(436412751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4096756291/5000000000 : ℝ)*x 0 + (167431609/625000000 : ℝ)*x 1 + (70091137/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096756291/5000000000 : ℝ)^19 ≤ (38847716520907/50000000000000 : ℝ)^15 := by
    have hnat : (4096756291 : ℕ)^19*50000000000000^15 ≤ 38847716520907^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096756291 5000000000 38847716520907 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167431609/625000000 : ℝ)^19 ≤ (4713600353049/25000000000000 : ℝ)^15 := by
    have hnat : (167431609 : ℕ)^19*25000000000000^15 ≤ 4713600353049^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167431609 625000000 4713600353049 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70091137/1000000000 : ℝ)^19 ≤ (862541384821/25000000000000 : ℝ)^15 := by
    have hnat : (70091137 : ℕ)^19*25000000000000^15 ≤ 862541384821^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70091137 1000000000 862541384821 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096756291/5000000000 : ℝ), (167431609/625000000 : ℝ), (70091137/1000000000 : ℝ)] ![(38847716520907/50000000000000 : ℝ), (4713600353049/25000000000000 : ℝ), (862541384821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096756291/5000000000 : ℝ)|^19 ≤ (38847716520907/50000000000000 : ℝ)^15
        have hw : |(4096756291/5000000000 : ℝ)|=(4096756291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167431609/625000000 : ℝ)|^19 ≤ (4713600353049/25000000000000 : ℝ)^15
        have hw : |(167431609/625000000 : ℝ)|=(167431609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70091137/1000000000 : ℝ)|^19 ≤ (862541384821/25000000000000 : ℝ)^15
        have hw : |(70091137/1000000000 : ℝ)|=(70091137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-96302951/1250000000 : ℝ)*x 0 + (223058921/312500000 : ℝ)*x 1 + (3953659251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96302951/1250000000 : ℝ)^19 ≤ (777834974177/20000000000000 : ℝ)^15 := by
    have hnat : (96302951 : ℕ)^19*20000000000000^15 ≤ 777834974177^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96302951 1250000000 777834974177 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223058921/312500000 : ℝ)^19 ≤ (65241128134219/100000000000000 : ℝ)^15 := by
    have hnat : (223058921 : ℕ)^19*100000000000000^15 ≤ 65241128134219^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223058921 312500000 65241128134219 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3953659251/10000000000 : ℝ)^19 ≤ (15434848487879/50000000000000 : ℝ)^15 := by
    have hnat : (3953659251 : ℕ)^19*50000000000000^15 ≤ 15434848487879^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3953659251 10000000000 15434848487879 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96302951/1250000000 : ℝ), (223058921/312500000 : ℝ), (3953659251/10000000000 : ℝ)] ![(777834974177/20000000000000 : ℝ), (65241128134219/100000000000000 : ℝ), (15434848487879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96302951/1250000000 : ℝ)|^19 ≤ (777834974177/20000000000000 : ℝ)^15
        have hw : |(-96302951/1250000000 : ℝ)|=(96302951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223058921/312500000 : ℝ)|^19 ≤ (65241128134219/100000000000000 : ℝ)^15
        have hw : |(223058921/312500000 : ℝ)|=(223058921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3953659251/10000000000 : ℝ)|^19 ≤ (15434848487879/50000000000000 : ℝ)^15
        have hw : |(3953659251/10000000000 : ℝ)|=(3953659251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (685723721/1000000000 : ℝ)*x 0 + (-6176793/2500000000 : ℝ)*x 1 + (930567211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685723721/1000000000 : ℝ)^19 ≤ (15502281826533/25000000000000 : ℝ)^15 := by
    have hnat : (685723721 : ℕ)^19*25000000000000^15 ≤ 15502281826533^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685723721 1000000000 15502281826533 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6176793/2500000000 : ℝ)^19 ≤ (12459937319/25000000000000 : ℝ)^15 := by
    have hnat : (6176793 : ℕ)^19*25000000000000^15 ≤ 12459937319^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6176793 2500000000 12459937319 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (930567211/2000000000 : ℝ)^19 ≤ (4742629116963/12500000000000 : ℝ)^15 := by
    have hnat : (930567211 : ℕ)^19*12500000000000^15 ≤ 4742629116963^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930567211 2000000000 4742629116963 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685723721/1000000000 : ℝ), (-6176793/2500000000 : ℝ), (930567211/2000000000 : ℝ)] ![(15502281826533/25000000000000 : ℝ), (12459937319/25000000000000 : ℝ), (4742629116963/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685723721/1000000000 : ℝ)|^19 ≤ (15502281826533/25000000000000 : ℝ)^15
        have hw : |(685723721/1000000000 : ℝ)|=(685723721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6176793/2500000000 : ℝ)|^19 ≤ (12459937319/25000000000000 : ℝ)^15
        have hw : |(-6176793/2500000000 : ℝ)|=(6176793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(930567211/2000000000 : ℝ)|^19 ≤ (4742629116963/12500000000000 : ℝ)^15
        have hw : |(930567211/2000000000 : ℝ)|=(930567211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2609086821/10000000000 : ℝ)*x 0 + (307956097/400000000 : ℝ)*x 1 + (-202375069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2609086821/10000000000 : ℝ)^19 ≤ (4558536970931/25000000000000 : ℝ)^15 := by
    have hnat : (2609086821 : ℕ)^19*25000000000000^15 ≤ 4558536970931^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609086821 10000000000 4558536970931 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307956097/400000000 : ℝ)^19 ≤ (71803095295143/100000000000000 : ℝ)^15 := by
    have hnat : (307956097 : ℕ)^19*100000000000000^15 ≤ 71803095295143^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307956097 400000000 71803095295143 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202375069/1250000000 : ℝ)^19 ≤ (9962756808981/100000000000000 : ℝ)^15 := by
    have hnat : (202375069 : ℕ)^19*100000000000000^15 ≤ 9962756808981^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202375069 1250000000 9962756808981 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2609086821/10000000000 : ℝ), (307956097/400000000 : ℝ), (-202375069/1250000000 : ℝ)] ![(4558536970931/25000000000000 : ℝ), (71803095295143/100000000000000 : ℝ), (9962756808981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2609086821/10000000000 : ℝ)|^19 ≤ (4558536970931/25000000000000 : ℝ)^15
        have hw : |(2609086821/10000000000 : ℝ)|=(2609086821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307956097/400000000 : ℝ)|^19 ≤ (71803095295143/100000000000000 : ℝ)^15
        have hw : |(307956097/400000000 : ℝ)|=(307956097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202375069/1250000000 : ℝ)|^19 ≤ (9962756808981/100000000000000 : ℝ)^15
        have hw : |(-202375069/1250000000 : ℝ)|=(202375069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (804526301/1000000000 : ℝ)*x 0 + (1066884749/5000000000 : ℝ)*x 1 + (808507943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804526301/1000000000 : ℝ)^19 ≤ (15183817470643/20000000000000 : ℝ)^15 := by
    have hnat : (804526301 : ℕ)^19*20000000000000^15 ≤ 15183817470643^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804526301 1000000000 15183817470643 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066884749/5000000000 : ℝ)^19 ≤ (7066811509449/50000000000000 : ℝ)^15 := by
    have hnat : (1066884749 : ℕ)^19*50000000000000^15 ≤ 7066811509449^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066884749 5000000000 7066811509449 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808507943/5000000000 : ℝ)^19 ≤ (4973644811769/50000000000000 : ℝ)^15 := by
    have hnat : (808507943 : ℕ)^19*50000000000000^15 ≤ 4973644811769^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808507943 5000000000 4973644811769 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804526301/1000000000 : ℝ), (1066884749/5000000000 : ℝ), (808507943/5000000000 : ℝ)] ![(15183817470643/20000000000000 : ℝ), (7066811509449/50000000000000 : ℝ), (4973644811769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804526301/1000000000 : ℝ)|^19 ≤ (15183817470643/20000000000000 : ℝ)^15
        have hw : |(804526301/1000000000 : ℝ)|=(804526301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1066884749/5000000000 : ℝ)|^19 ≤ (7066811509449/50000000000000 : ℝ)^15
        have hw : |(1066884749/5000000000 : ℝ)|=(1066884749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808507943/5000000000 : ℝ)|^19 ≤ (4973644811769/50000000000000 : ℝ)^15
        have hw : |(808507943/5000000000 : ℝ)|=(808507943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315055_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20187/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20187/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78217/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78217/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15823/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15823/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5887/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5887/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29829/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (20187/25000 : ℝ) ^ (75/16 : ℝ) ≤ (18350596952754346187/50000000000000000000 : ℝ) := by
    have hpowers : (20187/25000 : ℝ)^75 ≤ (18350596952754346187/50000000000000000000 : ℝ)^16 := by
      have hnat : (20187 : ℕ)^75*50000000000000000000^16 ≤ 18350596952754346187^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20187 25000 18350596952754346187 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20187/25000 : ℝ)) (X := (18350596952754346187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (68350596952754346187/50000000000000000000 : ℝ) ≤ (334052541791007/312500000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (68350596952754346187/50000000000000000000 : ℝ)^16 ≤ (334052541791007/312500000000000 : ℝ)^75 := by
      have hnat : (68350596952754346187 : ℕ)^16*312500000000000^75 ≤ 334052541791007^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68350596952754346187 50000000000000000000 334052541791007 312500000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (334052541791007/312500000000000 : ℝ)) (X := (68350596952754346187/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (43350596952754346187/25000000000000000000 : ℝ) ≤ (11246008714169233/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (43350596952754346187/25000000000000000000 : ℝ)^16 ≤ (11246008714169233/10000000000000000 : ℝ)^75 := by
      have hnat : (43350596952754346187 : ℕ)^16*10000000000000000^75 ≤ 11246008714169233^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43350596952754346187 25000000000000000000 11246008714169233 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11246008714169233/10000000000000000 : ℝ)) (X := (43350596952754346187/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(21552541791007/252337500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(556327376857009/8074800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (20187/25000 : ℝ)) (alpha := (21552541791007/252337500000000 : ℝ)) (beta := (556327376857009/8074800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20187/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(21552541791007/252337500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(556327376857009/8074800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (78217/100000 : ℝ) ^ (75/16 : ℝ) ≤ (3161179539877885811/10000000000000000000 : ℝ) := by
    have hpowers : (78217/100000 : ℝ)^75 ≤ (3161179539877885811/10000000000000000000 : ℝ)^16 := by
      have hnat : (78217 : ℕ)^75*10000000000000000000^16 ≤ 3161179539877885811^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78217 100000 3161179539877885811 10000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78217/100000 : ℝ)) (X := (3161179539877885811/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (13161179539877885811/10000000000000000000 : ℝ) ≤ (2650876950355537/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (13161179539877885811/10000000000000000000 : ℝ)^16 ≤ (2650876950355537/2500000000000000 : ℝ)^75 := by
      have hnat : (13161179539877885811 : ℕ)^16*2500000000000000^75 ≤ 2650876950355537^75*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13161179539877885811 10000000000000000000 2650876950355537 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2650876950355537/2500000000000000 : ℝ)) (X := (13161179539877885811/10000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (8161179539877885811/5000000000000000000 : ℝ) ≤ (11101807465644763/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (8161179539877885811/5000000000000000000 : ℝ)^16 ≤ (11101807465644763/10000000000000000 : ℝ)^75 := by
      have hnat : (8161179539877885811 : ℕ)^16*10000000000000000^75 ≤ 11101807465644763^75*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8161179539877885811 5000000000000000000 11101807465644763 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11101807465644763/10000000000000000 : ℝ)) (X := (8161179539877885811/5000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(150876950355537/1955425000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(99659932844523/1564340000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (78217/100000 : ℝ)) (alpha := (150876950355537/1955425000000000 : ℝ)) (beta := (99659932844523/1564340000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (78217/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(150876950355537/1955425000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(99659932844523/1564340000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (15823/20000 : ℝ) ^ (75/16 : ℝ) ≤ (33349419364332397941/100000000000000000000 : ℝ) := by
    have hpowers : (15823/20000 : ℝ)^75 ≤ (33349419364332397941/100000000000000000000 : ℝ)^16 := by
      have hnat : (15823 : ℕ)^75*100000000000000000000^16 ≤ 33349419364332397941^16*20000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15823 20000 33349419364332397941 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15823/20000 : ℝ)) (X := (33349419364332397941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (133349419364332397941/100000000000000000000 : ℝ) ≤ (10633219381028667/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (133349419364332397941/100000000000000000000 : ℝ)^16 ≤ (10633219381028667/10000000000000000 : ℝ)^75 := by
      have hnat : (133349419364332397941 : ℕ)^16*10000000000000000^75 ≤ 10633219381028667^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133349419364332397941 100000000000000000000 10633219381028667 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10633219381028667/10000000000000000 : ℝ)) (X := (133349419364332397941/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (83349419364332397941/50000000000000000000 : ℝ) ≤ (11151816532276409/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (83349419364332397941/50000000000000000000 : ℝ)^16 ≤ (11151816532276409/10000000000000000 : ℝ)^75 := by
      have hnat : (83349419364332397941 : ℕ)^16*10000000000000000^75 ≤ 11151816532276409^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83349419364332397941 50000000000000000000 11151816532276409 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11151816532276409/10000000000000000 : ℝ)) (X := (83349419364332397941/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(633219381028667/7911500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(259298575623871/3955750000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (15823/20000 : ℝ)) (alpha := (633219381028667/7911500000000000 : ℝ)) (beta := (259298575623871/3955750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15823/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(633219381028667/7911500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(259298575623871/3955750000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-731759467/5000000000 : ℝ)*X 0 0+(2905889331/5000000000 : ℝ)*X 0 1+(4941411657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((484631203/1000000000 : ℝ)*X 1 0+(-441620073/10000000000 : ℝ)*X 1 1+(1629021401/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2413311291/5000000000 : ℝ)*X 2 0+(5947581503/10000000000 : ℝ)*X 2 1+(-712452797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((259363243/400000000 : ℝ)*X 0 0+(376478137/1000000000 : ℝ)*X 0 1+(12650681/62500000 : ℝ)*X 0 2+(259363243/400000000 : ℝ)*X 1 0+(376478137/1000000000 : ℝ)*X 1 1+(12650681/62500000 : ℝ)*X 1 2+(259363243/400000000 : ℝ)*X 2 0+(376478137/1000000000 : ℝ)*X 2 1+(12650681/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-210189599/1250000000 : ℝ)*X 0 0+(1889867213/5000000000 : ℝ)*X 0 1+(335764293/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((716994577/2000000000 : ℝ)*X 1 0+(-5841/50000000 : ℝ)*X 1 1+(972148259/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3561912281/10000000000 : ℝ)*X 2 0+(7481959037/10000000000 : ℝ)*X 2 1+(-370519757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((834780509/2000000000 : ℝ)*X 0 0+(6747353041/10000000000 : ℝ)*X 0 1+(1110916063/10000000000 : ℝ)*X 0 2+(834780509/2000000000 : ℝ)*X 1 0+(6747353041/10000000000 : ℝ)*X 1 1+(1110916063/10000000000 : ℝ)*X 1 2+(834780509/2000000000 : ℝ)*X 2 0+(6747353041/10000000000 : ℝ)*X 2 1+(1110916063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-58903739/1250000000 : ℝ)*X 0 0+(4351267623/10000000000 : ℝ)*X 0 1+(1389762671/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((59676717/200000000 : ℝ)*X 1 0+(-627906487/10000000000 : ℝ)*X 1 1+(8000592377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6825627323/10000000000 : ℝ)*X 2 0+(2254400059/5000000000 : ℝ)*X 2 1+(-436412751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4096756291/5000000000 : ℝ)*X 0 0+(167431609/625000000 : ℝ)*X 0 1+(70091137/1000000000 : ℝ)*X 0 2+(4096756291/5000000000 : ℝ)*X 1 0+(167431609/625000000 : ℝ)*X 1 1+(70091137/1000000000 : ℝ)*X 1 2+(4096756291/5000000000 : ℝ)*X 2 0+(167431609/625000000 : ℝ)*X 2 1+(70091137/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-96302951/1250000000 : ℝ)*X 0 0+(223058921/312500000 : ℝ)*X 0 1+(3953659251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((685723721/1000000000 : ℝ)*X 1 0+(-6176793/2500000000 : ℝ)*X 1 1+(930567211/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2609086821/10000000000 : ℝ)*X 2 0+(307956097/400000000 : ℝ)*X 2 1+(-202375069/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((804526301/1000000000 : ℝ)*X 0 0+(1066884749/5000000000 : ℝ)*X 0 1+(808507943/5000000000 : ℝ)*X 0 2+(804526301/1000000000 : ℝ)*X 1 0+(1066884749/5000000000 : ℝ)*X 1 1+(808507943/5000000000 : ℝ)*X 1 2+(804526301/1000000000 : ℝ)*X 2 0+(1066884749/5000000000 : ℝ)*X 2 1+(808507943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((29969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80896688196731602555465251/6188137955000000000000000000000 : ℝ) := by norm_num
    linear_combination (13883739563/20000000000 : ℝ)*(base7) + (1972277/1000000000000 : ℝ)*(base49) + (252899/250000000000 : ℝ)*(base60) + (452030203527/200000000000 : ℝ)*(major_s1_0) + (452030203527/200000000000 : ℝ)*(major_s1_1) + (452030203527/200000000000 : ℝ)*(major_s1_2) + (1001509/62500000000 : ℝ)*(sp_s1_0) + (1132687/1000000000000 : ℝ)*(sp_s1_6) + (282229415643/100000000000 : ℝ)*(sp_s1_7) + (56446971897/20000000000 : ℝ)*(sp_s1_8) + (2822337350493/1000000000000 : ℝ)*(sp_s1_9) + (1988222235019/1000000000000 : ℝ)*(sp_s1_13) + (1536571/40000000000 : ℝ)*(sp_s1_14) + (11244357/1000000000000 : ℝ)*(sp_s1_23) + (323509097389/250000000000 : ℝ)*(f.failure) + (56446971897/20000000000 : ℝ)*(f.sum) + (28652553700309379847/123762759100000000000000000000000 : ℝ)*base62 + (245123182902787/791150000000000000000000000 : ℝ)*base65 + (135198896015079/312868000000000000000000000 : ℝ)*base67 + (796072397781391/1582300000000000000000000000 : ℝ)*base68 + (634144354968899129/2661824175000000000000000000000 : ℝ)*base71 + (223448584588363/538320000000000000000000000 : ℝ)*base72 + (18455366287209/97771250000000000000000000 : ℝ)*base74 + (32696985565363/67290000000000000000000000 : ℝ)*base76 + (9727170325758057353/42105775440000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (9649/25000000000000000 : ℝ)*base86 + (9649/25000000000000000 : ℝ)*base88 + (9649/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5887/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5887/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17328078881947932815035003853963/1040999507479875000000000000000000000 : ℝ) := by norm_num
    linear_combination (146992208037/250000000000 : ℝ)*(base7) + (8616619/1000000000000 : ℝ)*(base27) + (720411/500000000000 : ℝ)*(base59) + (513099913601/250000000000 : ℝ)*(major_s1_0) + (513099913601/250000000000 : ℝ)*(major_s1_1) + (513099913601/250000000000 : ℝ)*(major_s1_2) + (4789353/500000000000 : ℝ)*(sp_s1_0) + (4334227/500000000000 : ℝ)*(sp_s1_2) + (14035747/100000000000 : ℝ)*(sp_s1_8) + (2587584968129/1000000000000 : ℝ)*(sp_s1_14) + (517490837873/200000000000 : ℝ)*(sp_s1_15) + (129379293919/50000000000 : ℝ)*(sp_s1_16) + (440753306177/250000000000 : ℝ)*(sp_s1_20) + (36539257/1000000000000 : ℝ)*(sp_s1_27) + (293772387109/250000000000 : ℝ)*(f.failure) + (517518909367/200000000000 : ℝ)*(f.sum) + (43854590164611752617/77351724437500000000000000000000 : ℝ)*base63 + (2620333462188609/3955750000000000000000000000 : ℝ)*base65 + (305035896513471/782170000000000000000000000 : ℝ)*base67 + (465903689941223/494468750000000000000000000 : ℝ)*base69 + (21764034393457721113/79854725250000000000000000000000 : ℝ)*base71 + (914186831029319/2018700000000000000000000000 : ℝ)*base73 + (2955018891462703/1955425000000000000000000000 : ℝ)*base75 + (270310395025103/252337500000000000000000000 : ℝ)*base77 + (8274612037437213007/157896657900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (29169/25000000000000000 : ℝ)*base86 + (29169/25000000000000000 : ℝ)*base88 + (29169/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29829/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (75661970839815971833063102213997/8327996059839000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731708390993/1000000000000 : ℝ)*(base7) + (93943849033/1000000000000 : ℝ)*(base40) + (178601/1000000000000 : ℝ)*(base49) + (123533/200000000000 : ℝ)*(base59) + (1956618755897/1000000000000 : ℝ)*(major_s1_0) + (1956618755897/1000000000000 : ℝ)*(major_s1_1) + (1956618755897/1000000000000 : ℝ)*(major_s1_2) + (191487/500000000000 : ℝ)*(sp_s1_1) + (44664489/1000000000000 : ℝ)*(sp_s1_9) + (7760403/250000000000 : ℝ)*(sp_s1_20) + (591809801739/250000000000 : ℝ)*(sp_s1_21) + (1183619411991/500000000000 : ℝ)*(sp_s1_22) + (591798635617/250000000000 : ℝ)*(sp_s1_23) + (28936376539/15625000000 : ℝ)*(sp_s1_27) + (224050149823/200000000000 : ℝ)*(f.failure) + (591809801739/250000000000 : ℝ)*(f.sum) + (197334917526523344023/618813795500000000000000000000000 : ℝ)*base63 + (2687810674255687/3955750000000000000000000000 : ℝ)*base65 + (602800268426101/1564340000000000000000000000 : ℝ)*base67 + (4624353776967699/7911500000000000000000000000 : ℝ)*base69 + (50056162737406561759/79854725250000000000000000000000 : ℝ)*base71 + (282040784181113/8074800000000000000000000000 : ℝ)*base73 + (570653731935993/3910850000000000000000000000 : ℝ)*base75 + (213819209394499/1009350000000000000000000000 : ℝ)*base76 + (76528908581617867661/631586631600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (4643/20000000000000000 : ℝ)*base86 + (4643/20000000000000000 : ℝ)*base88 + (4643/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20187/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20187/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78217/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78217/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15823/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15823/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5887/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5887/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29829/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315055_s1 p hpa hpb X hX hprev0

#print axioms solution
