-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302055_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:49.334859+00:00
-- url     : https://prove2.me/submissions/4a5b84e7-a915-4802-bd3c-5e750b7e775e

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
theorem collision_support_c302055_s4_s4_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1594948549/10000000000 : ℝ)*x 0 + (5964299331/10000000000 : ℝ)*x 1 + (1014282747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1594948549/10000000000 : ℝ)^131 ≤ (8811475424641/100000000000000 : ℝ)^99 := by
    have hnat : (1594948549 : ℕ)^131*100000000000000^99 ≤ 8811475424641^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594948549 10000000000 8811475424641 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5964299331/10000000000 : ℝ)^131 ≤ (25233819327223/50000000000000 : ℝ)^99 := by
    have hnat : (5964299331 : ℕ)^131*50000000000000^99 ≤ 25233819327223^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964299331 10000000000 25233819327223 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014282747/2000000000 : ℝ)^131 ≤ (40720885916957/100000000000000 : ℝ)^99 := by
    have hnat : (1014282747 : ℕ)^131*100000000000000^99 ≤ 40720885916957^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014282747 2000000000 40720885916957 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1594948549/10000000000 : ℝ), (5964299331/10000000000 : ℝ), (1014282747/2000000000 : ℝ)] ![(8811475424641/100000000000000 : ℝ), (25233819327223/50000000000000 : ℝ), (40720885916957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1594948549/10000000000 : ℝ)|^131 ≤ (8811475424641/100000000000000 : ℝ)^99
        have hw : |(-1594948549/10000000000 : ℝ)|=(1594948549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5964299331/10000000000 : ℝ)|^131 ≤ (25233819327223/50000000000000 : ℝ)^99
        have hw : |(5964299331/10000000000 : ℝ)|=(5964299331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1014282747/2000000000 : ℝ)|^131 ≤ (40720885916957/100000000000000 : ℝ)^99
        have hw : |(1014282747/2000000000 : ℝ)|=(1014282747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4903895899/10000000000 : ℝ)*x 0 + (6150733171/10000000000 : ℝ)*x 1 + (-77496229/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4903895899/10000000000 : ℝ)^131 ≤ (19475300768021/50000000000000 : ℝ)^99 := by
    have hnat : (4903895899 : ℕ)^131*50000000000000^99 ≤ 19475300768021^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4903895899 10000000000 19475300768021 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6150733171/10000000000 : ℝ)^131 ≤ (52565552600493/100000000000000 : ℝ)^99 := by
    have hnat : (6150733171 : ℕ)^131*100000000000000^99 ≤ 52565552600493^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6150733171 10000000000 52565552600493 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77496229/500000000 : ℝ)^131 ≤ (8483845848621/100000000000000 : ℝ)^99 := by
    have hnat : (77496229 : ℕ)^131*100000000000000^99 ≤ 8483845848621^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77496229 500000000 8483845848621 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4903895899/10000000000 : ℝ), (6150733171/10000000000 : ℝ), (-77496229/500000000 : ℝ)] ![(19475300768021/50000000000000 : ℝ), (52565552600493/100000000000000 : ℝ), (8483845848621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4903895899/10000000000 : ℝ)|^131 ≤ (19475300768021/50000000000000 : ℝ)^99
        have hw : |(4903895899/10000000000 : ℝ)|=(4903895899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6150733171/10000000000 : ℝ)|^131 ≤ (52565552600493/100000000000000 : ℝ)^99
        have hw : |(6150733171/10000000000 : ℝ)|=(6150733171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77496229/500000000 : ℝ)|^131 ≤ (8483845848621/100000000000000 : ℝ)^99
        have hw : |(-77496229/500000000 : ℝ)|=(77496229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-931162547/5000000000 : ℝ)*x 0 + (789522491/2000000000 : ℝ)*x 1 + (54345657/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931162547/5000000000 : ℝ)^131 ≤ (5408587267783/50000000000000 : ℝ)^99 := by
    have hnat : (931162547 : ℕ)^131*50000000000000^99 ≤ 5408587267783^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931162547 5000000000 5408587267783 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (789522491/2000000000 : ℝ)^131 ≤ (14615940988693/50000000000000 : ℝ)^99 := by
    have hnat : (789522491 : ℕ)^131*50000000000000^99 ≤ 14615940988693^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789522491 2000000000 14615940988693 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54345657/80000000 : ℝ)^131 ≤ (29975471736101/50000000000000 : ℝ)^99 := by
    have hnat : (54345657 : ℕ)^131*50000000000000^99 ≤ 29975471736101^99*80000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54345657 80000000 29975471736101 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931162547/5000000000 : ℝ), (789522491/2000000000 : ℝ), (54345657/80000000 : ℝ)] ![(5408587267783/50000000000000 : ℝ), (14615940988693/50000000000000 : ℝ), (29975471736101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931162547/5000000000 : ℝ)|^131 ≤ (5408587267783/50000000000000 : ℝ)^99
        have hw : |(-931162547/5000000000 : ℝ)|=(931162547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(789522491/2000000000 : ℝ)|^131 ≤ (14615940988693/50000000000000 : ℝ)^99
        have hw : |(789522491/2000000000 : ℝ)|=(789522491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54345657/80000000 : ℝ)|^131 ≤ (29975471736101/50000000000000 : ℝ)^99
        have hw : |(54345657/80000000 : ℝ)|=(54345657/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (637639373/2000000000 : ℝ)*x 0 + (42501/2000000000 : ℝ)*x 1 + (258918909/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (637639373/2000000000 : ℝ)^131 ≤ (172133302019/781250000000 : ℝ)^99 := by
    have hnat : (637639373 : ℕ)^131*781250000000^99 ≤ 172133302019^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637639373 2000000000 172133302019 781250000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42501/2000000000 : ℝ)^131 ≤ (65618127/100000000000000 : ℝ)^99 := by
    have hnat : (42501 : ℕ)^131*100000000000000^99 ≤ 65618127^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42501 2000000000 65618127 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258918909/312500000 : ℝ)^131 ≤ (77966871715299/100000000000000 : ℝ)^99 := by
    have hnat : (258918909 : ℕ)^131*100000000000000^99 ≤ 77966871715299^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258918909 312500000 77966871715299 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(637639373/2000000000 : ℝ), (42501/2000000000 : ℝ), (258918909/312500000 : ℝ)] ![(172133302019/781250000000 : ℝ), (65618127/100000000000000 : ℝ), (77966871715299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(637639373/2000000000 : ℝ)|^131 ≤ (172133302019/781250000000 : ℝ)^99
        have hw : |(637639373/2000000000 : ℝ)|=(637639373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42501/2000000000 : ℝ)|^131 ≤ (65618127/100000000000000 : ℝ)^99
        have hw : |(42501/2000000000 : ℝ)|=(42501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258918909/312500000 : ℝ)|^131 ≤ (77966871715299/100000000000000 : ℝ)^99
        have hw : |(258918909/312500000 : ℝ)|=(258918909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1593395517/5000000000 : ℝ)*x 0 + (3937329341/5000000000 : ℝ)*x 1 + (-526437353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1593395517/5000000000 : ℝ)^131 ≤ (22020207779169/100000000000000 : ℝ)^99 := by
    have hnat : (1593395517 : ℕ)^131*100000000000000^99 ≤ 22020207779169^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593395517 5000000000 22020207779169 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3937329341/5000000000 : ℝ)^131 ≤ (72893781854341/100000000000000 : ℝ)^99 := by
    have hnat : (3937329341 : ℕ)^131*100000000000000^99 ≤ 72893781854341^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3937329341 5000000000 72893781854341 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526437353/5000000000 : ℝ)^131 ≤ (5086010348241/100000000000000 : ℝ)^99 := by
    have hnat : (526437353 : ℕ)^131*100000000000000^99 ≤ 5086010348241^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526437353 5000000000 5086010348241 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1593395517/5000000000 : ℝ), (3937329341/5000000000 : ℝ), (-526437353/5000000000 : ℝ)] ![(22020207779169/100000000000000 : ℝ), (72893781854341/100000000000000 : ℝ), (5086010348241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1593395517/5000000000 : ℝ)|^131 ≤ (22020207779169/100000000000000 : ℝ)^99
        have hw : |(1593395517/5000000000 : ℝ)|=(1593395517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3937329341/5000000000 : ℝ)|^131 ≤ (72893781854341/100000000000000 : ℝ)^99
        have hw : |(3937329341/5000000000 : ℝ)|=(3937329341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526437353/5000000000 : ℝ)|^131 ≤ (5086010348241/100000000000000 : ℝ)^99
        have hw : |(-526437353/5000000000 : ℝ)|=(526437353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4519167979/10000000000 : ℝ)*x 0 + (6634236259/10000000000 : ℝ)*x 1 + (665757451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4519167979/10000000000 : ℝ)^131 ≤ (34959260477971/100000000000000 : ℝ)^99 := by
    have hnat : (4519167979 : ℕ)^131*100000000000000^99 ≤ 34959260477971^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519167979 10000000000 34959260477971 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6634236259/10000000000 : ℝ)^131 ≤ (29050794039467/50000000000000 : ℝ)^99 := by
    have hnat : (6634236259 : ℕ)^131*50000000000000^99 ≤ 29050794039467^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6634236259 10000000000 29050794039467 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (665757451/5000000000 : ℝ)^131 ≤ (1387830284953/20000000000000 : ℝ)^99 := by
    have hnat : (665757451 : ℕ)^131*20000000000000^99 ≤ 1387830284953^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665757451 5000000000 1387830284953 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4519167979/10000000000 : ℝ), (6634236259/10000000000 : ℝ), (665757451/5000000000 : ℝ)] ![(34959260477971/100000000000000 : ℝ), (29050794039467/50000000000000 : ℝ), (1387830284953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4519167979/10000000000 : ℝ)|^131 ≤ (34959260477971/100000000000000 : ℝ)^99
        have hw : |(4519167979/10000000000 : ℝ)|=(4519167979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6634236259/10000000000 : ℝ)|^131 ≤ (29050794039467/50000000000000 : ℝ)^99
        have hw : |(6634236259/10000000000 : ℝ)|=(6634236259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(665757451/5000000000 : ℝ)|^131 ≤ (1387830284953/20000000000000 : ℝ)^99
        have hw : |(665757451/5000000000 : ℝ)|=(665757451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-752110951/10000000000 : ℝ)*x 0 + (215550007/500000000 : ℝ)*x 1 + (1425690887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (752110951/10000000000 : ℝ)^131 ≤ (3258816481011/100000000000000 : ℝ)^99 := by
    have hnat : (752110951 : ℕ)^131*100000000000000^99 ≤ 3258816481011^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752110951 10000000000 3258816481011 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215550007/500000000 : ℝ)^131 ≤ (8211109723351/25000000000000 : ℝ)^99 := by
    have hnat : (215550007 : ℕ)^131*25000000000000^99 ≤ 8211109723351^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215550007 500000000 8211109723351 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1425690887/2000000000 : ℝ)^131 ≤ (63896744609613/100000000000000 : ℝ)^99 := by
    have hnat : (1425690887 : ℕ)^131*100000000000000^99 ≤ 63896744609613^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425690887 2000000000 63896744609613 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-752110951/10000000000 : ℝ), (215550007/500000000 : ℝ), (1425690887/2000000000 : ℝ)] ![(3258816481011/100000000000000 : ℝ), (8211109723351/25000000000000 : ℝ), (63896744609613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-752110951/10000000000 : ℝ)|^131 ≤ (3258816481011/100000000000000 : ℝ)^99
        have hw : |(-752110951/10000000000 : ℝ)|=(752110951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215550007/500000000 : ℝ)|^131 ≤ (8211109723351/25000000000000 : ℝ)^99
        have hw : |(215550007/500000000 : ℝ)|=(215550007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1425690887/2000000000 : ℝ)|^131 ≤ (63896744609613/100000000000000 : ℝ)^99
        have hw : |(1425690887/2000000000 : ℝ)|=(1425690887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (326571491/1250000000 : ℝ)*x 0 + (-141263817/5000000000 : ℝ)*x 1 + (431072311/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326571491/1250000000 : ℝ)^131 ≤ (3385913584647/20000000000000 : ℝ)^99 := by
    have hnat : (326571491 : ℕ)^131*20000000000000^99 ≤ 3385913584647^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326571491 1250000000 3385913584647 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141263817/5000000000 : ℝ)^131 ≤ (892059369787/100000000000000 : ℝ)^99 := by
    have hnat : (141263817 : ℕ)^131*100000000000000^99 ≤ 892059369787^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141263817 5000000000 892059369787 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431072311/500000000 : ℝ)^131 ≤ (82178372698477/100000000000000 : ℝ)^99 := by
    have hnat : (431072311 : ℕ)^131*100000000000000^99 ≤ 82178372698477^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431072311 500000000 82178372698477 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326571491/1250000000 : ℝ), (-141263817/5000000000 : ℝ), (431072311/500000000 : ℝ)] ![(3385913584647/20000000000000 : ℝ), (892059369787/100000000000000 : ℝ), (82178372698477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326571491/1250000000 : ℝ)|^131 ≤ (3385913584647/20000000000000 : ℝ)^99
        have hw : |(326571491/1250000000 : ℝ)|=(326571491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141263817/5000000000 : ℝ)|^131 ≤ (892059369787/100000000000000 : ℝ)^99
        have hw : |(-141263817/5000000000 : ℝ)|=(141263817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(431072311/500000000 : ℝ)|^131 ≤ (82178372698477/100000000000000 : ℝ)^99
        have hw : |(431072311/500000000 : ℝ)|=(431072311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6952902243/10000000000 : ℝ)*x 0 + (2266017787/5000000000 : ℝ)*x 1 + (-90223389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6952902243/10000000000 : ℝ)^131 ≤ (61822862913863/100000000000000 : ℝ)^99 := by
    have hnat : (6952902243 : ℕ)^131*100000000000000^99 ≤ 61822862913863^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6952902243 10000000000 61822862913863 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266017787/5000000000 : ℝ)^131 ≤ (35091036658189/100000000000000 : ℝ)^99 := by
    have hnat : (2266017787 : ℕ)^131*100000000000000^99 ≤ 35091036658189^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266017787 5000000000 35091036658189 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90223389/1250000000 : ℝ)^131 ≤ (308610040729/10000000000000 : ℝ)^99 := by
    have hnat : (90223389 : ℕ)^131*10000000000000^99 ≤ 308610040729^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90223389 1250000000 308610040729 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6952902243/10000000000 : ℝ), (2266017787/5000000000 : ℝ), (-90223389/1250000000 : ℝ)] ![(61822862913863/100000000000000 : ℝ), (35091036658189/100000000000000 : ℝ), (308610040729/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6952902243/10000000000 : ℝ)|^131 ≤ (61822862913863/100000000000000 : ℝ)^99
        have hw : |(6952902243/10000000000 : ℝ)|=(6952902243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266017787/5000000000 : ℝ)|^131 ≤ (35091036658189/100000000000000 : ℝ)^99
        have hw : |(2266017787/5000000000 : ℝ)|=(2266017787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90223389/1250000000 : ℝ)|^131 ≤ (308610040729/10000000000000 : ℝ)^99
        have hw : |(-90223389/1250000000 : ℝ)|=(90223389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2120796443/2500000000 : ℝ)*x 0 + (1209509851/5000000000 : ℝ)*x 1 + (922659353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120796443/2500000000 : ℝ)^131 ≤ (4021952473801/5000000000000 : ℝ)^99 := by
    have hnat : (2120796443 : ℕ)^131*5000000000000^99 ≤ 4021952473801^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120796443 2500000000 4021952473801 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209509851/5000000000 : ℝ)^131 ≤ (15290149742263/100000000000000 : ℝ)^99 := by
    have hnat : (1209509851 : ℕ)^131*100000000000000^99 ≤ 15290149742263^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209509851 5000000000 15290149742263 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922659353/10000000000 : ℝ)^131 ≤ (4270800767681/100000000000000 : ℝ)^99 := by
    have hnat : (922659353 : ℕ)^131*100000000000000^99 ≤ 4270800767681^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922659353 10000000000 4270800767681 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120796443/2500000000 : ℝ), (1209509851/5000000000 : ℝ), (922659353/10000000000 : ℝ)] ![(4021952473801/5000000000000 : ℝ), (15290149742263/100000000000000 : ℝ), (4270800767681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120796443/2500000000 : ℝ)|^131 ≤ (4021952473801/5000000000000 : ℝ)^99
        have hw : |(2120796443/2500000000 : ℝ)|=(2120796443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209509851/5000000000 : ℝ)|^131 ≤ (15290149742263/100000000000000 : ℝ)^99
        have hw : |(1209509851/5000000000 : ℝ)|=(1209509851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922659353/10000000000 : ℝ)|^131 ≤ (4270800767681/100000000000000 : ℝ)^99
        have hw : |(922659353/10000000000 : ℝ)|=(922659353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007309857/10000000000 : ℝ)*x 0 + (3857381377/5000000000 : ℝ)*x 1 + (3428992567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007309857/10000000000 : ℝ)^131 ≤ (1199204308277/25000000000000 : ℝ)^99 := by
    have hnat : (1007309857 : ℕ)^131*25000000000000^99 ≤ 1199204308277^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007309857 10000000000 1199204308277 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3857381377/5000000000 : ℝ)^131 ≤ (35470849824691/50000000000000 : ℝ)^99 := by
    have hnat : (3857381377 : ℕ)^131*50000000000000^99 ≤ 35470849824691^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857381377 5000000000 35470849824691 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3428992567/10000000000 : ℝ)^131 ≤ (12130741550537/50000000000000 : ℝ)^99 := by
    have hnat : (3428992567 : ℕ)^131*50000000000000^99 ≤ 12130741550537^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3428992567 10000000000 12130741550537 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007309857/10000000000 : ℝ), (3857381377/5000000000 : ℝ), (3428992567/10000000000 : ℝ)] ![(1199204308277/25000000000000 : ℝ), (35470849824691/50000000000000 : ℝ), (12130741550537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007309857/10000000000 : ℝ)|^131 ≤ (1199204308277/25000000000000 : ℝ)^99
        have hw : |(-1007309857/10000000000 : ℝ)|=(1007309857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3857381377/5000000000 : ℝ)|^131 ≤ (35470849824691/50000000000000 : ℝ)^99
        have hw : |(3857381377/5000000000 : ℝ)|=(3857381377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3428992567/10000000000 : ℝ)|^131 ≤ (12130741550537/50000000000000 : ℝ)^99
        have hw : |(3428992567/10000000000 : ℝ)|=(3428992567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6984090147/10000000000 : ℝ)*x 0 + (-36919/9765625 : ℝ)*x 1 + (957799823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6984090147/10000000000 : ℝ)^131 ≤ (62190077299859/100000000000000 : ℝ)^99 := by
    have hnat : (6984090147 : ℕ)^131*100000000000000^99 ≤ 62190077299859^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6984090147 10000000000 62190077299859 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36919/9765625 : ℝ)^131 ≤ (62306837353/100000000000000 : ℝ)^99 := by
    have hnat : (36919 : ℕ)^131*100000000000000^99 ≤ 62306837353^99*9765625^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36919 9765625 62306837353 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957799823/2000000000 : ℝ)^131 ≤ (7549523169749/20000000000000 : ℝ)^99 := by
    have hnat : (957799823 : ℕ)^131*20000000000000^99 ≤ 7549523169749^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957799823 2000000000 7549523169749 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6984090147/10000000000 : ℝ), (-36919/9765625 : ℝ), (957799823/2000000000 : ℝ)] ![(62190077299859/100000000000000 : ℝ), (62306837353/100000000000000 : ℝ), (7549523169749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6984090147/10000000000 : ℝ)|^131 ≤ (62190077299859/100000000000000 : ℝ)^99
        have hw : |(6984090147/10000000000 : ℝ)|=(6984090147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36919/9765625 : ℝ)|^131 ≤ (62306837353/100000000000000 : ℝ)^99
        have hw : |(-36919/9765625 : ℝ)|=(36919/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957799823/2000000000 : ℝ)|^131 ≤ (7549523169749/20000000000000 : ℝ)^99
        have hw : |(957799823/2000000000 : ℝ)|=(957799823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2388107319/10000000000 : ℝ)*x 0 + (813216773/1000000000 : ℝ)*x 1 + (-160749979/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2388107319/10000000000 : ℝ)^131 ≤ (3758034354687/25000000000000 : ℝ)^99 := by
    have hnat : (2388107319 : ℕ)^131*25000000000000^99 ≤ 3758034354687^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388107319 10000000000 3758034354687 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813216773/1000000000 : ℝ)^131 ≤ (4754032294527/6250000000000 : ℝ)^99 := by
    have hnat : (813216773 : ℕ)^131*6250000000000^99 ≤ 4754032294527^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813216773 1000000000 4754032294527 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160749979/1000000000 : ℝ)^131 ≤ (222583646331/2500000000000 : ℝ)^99 := by
    have hnat : (160749979 : ℕ)^131*2500000000000^99 ≤ 222583646331^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160749979 1000000000 222583646331 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2388107319/10000000000 : ℝ), (813216773/1000000000 : ℝ), (-160749979/1000000000 : ℝ)] ![(3758034354687/25000000000000 : ℝ), (4754032294527/6250000000000 : ℝ), (222583646331/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2388107319/10000000000 : ℝ)|^131 ≤ (3758034354687/25000000000000 : ℝ)^99
        have hw : |(2388107319/10000000000 : ℝ)|=(2388107319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(813216773/1000000000 : ℝ)|^131 ≤ (4754032294527/6250000000000 : ℝ)^99
        have hw : |(813216773/1000000000 : ℝ)|=(813216773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-160749979/1000000000 : ℝ)|^131 ≤ (222583646331/2500000000000 : ℝ)^99
        have hw : |(-160749979/1000000000 : ℝ)|=(160749979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s4_s4_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1033791789/1250000000 : ℝ)*x 0 + (2183503653/10000000000 : ℝ)*x 1 + (801385623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033791789/1250000000 : ℝ)^131 ≤ (77779268474399/100000000000000 : ℝ)^99 := by
    have hnat : (1033791789 : ℕ)^131*100000000000000^99 ≤ 77779268474399^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033791789 1250000000 77779268474399 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183503653/10000000000 : ℝ)^131 ≤ (417250755479/3125000000000 : ℝ)^99 := by
    have hnat : (2183503653 : ℕ)^131*3125000000000^99 ≤ 417250755479^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183503653 10000000000 417250755479 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801385623/5000000000 : ℝ)^131 ≤ (8868707343113/100000000000000 : ℝ)^99 := by
    have hnat : (801385623 : ℕ)^131*100000000000000^99 ≤ 8868707343113^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801385623 5000000000 8868707343113 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033791789/1250000000 : ℝ), (2183503653/10000000000 : ℝ), (801385623/5000000000 : ℝ)] ![(77779268474399/100000000000000 : ℝ), (417250755479/3125000000000 : ℝ), (8868707343113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033791789/1250000000 : ℝ)|^131 ≤ (77779268474399/100000000000000 : ℝ)^99
        have hw : |(1033791789/1250000000 : ℝ)|=(1033791789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2183503653/10000000000 : ℝ)|^131 ≤ (417250755479/3125000000000 : ℝ)^99
        have hw : |(2183503653/10000000000 : ℝ)|=(2183503653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801385623/5000000000 : ℝ)|^131 ≤ (8868707343113/100000000000000 : ℝ)^99
        have hw : |(801385623/5000000000 : ℝ)|=(801385623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302055_s4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((20133/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20133/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39459/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39459/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15793/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15793/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((71553/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71553/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70573/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70573/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71657/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71657/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (20133/25000 : ℝ) ^ (65/16 : ℝ) ≤ (41495114734984093391/100000000000000000000 : ℝ) := by
    have hpowers : (20133/25000 : ℝ)^65 ≤ (41495114734984093391/100000000000000000000 : ℝ)^16 := by
      have hnat : (20133 : ℕ)^65*100000000000000000000^16 ≤ 41495114734984093391^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20133 25000 41495114734984093391 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20133/25000 : ℝ)) (X := (41495114734984093391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (141495114734984093391/100000000000000000000 : ℝ) ≤ (10891948685796543/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (141495114734984093391/100000000000000000000 : ℝ)^16 ≤ (10891948685796543/10000000000000000 : ℝ)^65 := by
      have hnat : (141495114734984093391 : ℕ)^16*10000000000000000^65 ≤ 10891948685796543^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141495114734984093391 100000000000000000000 10891948685796543 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10891948685796543/10000000000000000 : ℝ)) (X := (141495114734984093391/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (91495114734984093391/50000000000000000000 : ℝ) ≤ (11603730599418919/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (91495114734984093391/50000000000000000000 : ℝ)^16 ≤ (11603730599418919/10000000000000000 : ℝ)^65 := by
      have hnat : (91495114734984093391 : ℕ)^16*10000000000000000^65 ≤ 11603730599418919^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91495114734984093391 50000000000000000000 11603730599418919 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11603730599418919/10000000000000000 : ℝ)) (X := (91495114734984093391/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(891948685796543/8053200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(88972739202797/1006650000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (20133/25000 : ℝ)) (alpha := (891948685796543/8053200000000000 : ℝ)) (beta := (88972739202797/1006650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20133/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(891948685796543/8053200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(88972739202797/1006650000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (39459/50000 : ℝ) ^ (65/16 : ℝ) ≤ (19109432539417596563/50000000000000000000 : ℝ) := by
    have hpowers : (39459/50000 : ℝ)^65 ≤ (19109432539417596563/50000000000000000000 : ℝ)^16 := by
      have hnat : (39459 : ℕ)^65*50000000000000000000^16 ≤ 19109432539417596563^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39459 50000 19109432539417596563 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39459/50000 : ℝ)) (X := (19109432539417596563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (69109432539417596563/50000000000000000000 : ℝ) ≤ (5414660000776289/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (69109432539417596563/50000000000000000000 : ℝ)^16 ≤ (5414660000776289/5000000000000000 : ℝ)^65 := by
      have hnat : (69109432539417596563 : ℕ)^16*5000000000000000^65 ≤ 5414660000776289^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69109432539417596563 50000000000000000000 5414660000776289 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5414660000776289/5000000000000000 : ℝ)) (X := (69109432539417596563/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (44109432539417596563/25000000000000000000 : ℝ) ≤ (1437505284205599/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (44109432539417596563/25000000000000000000 : ℝ)^16 ≤ (1437505284205599/1250000000000000 : ℝ)^65 := by
      have hnat : (44109432539417596563 : ℕ)^16*1250000000000000^65 ≤ 1437505284205599^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44109432539417596563 25000000000000000000 1437505284205599 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1437505284205599/1250000000000000 : ℝ)) (X := (44109432539417596563/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(138220000258763/1315300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(335361136046107/3945900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (39459/50000 : ℝ)) (alpha := (138220000258763/1315300000000000 : ℝ)) (beta := (335361136046107/3945900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39459/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(138220000258763/1315300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(335361136046107/3945900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (15793/20000 : ℝ) ^ (65/16 : ℝ) ≤ (38311417755097995799/100000000000000000000 : ℝ) := by
    have hpowers : (15793/20000 : ℝ)^65 ≤ (38311417755097995799/100000000000000000000 : ℝ)^16 := by
      have hnat : (15793 : ℕ)^65*100000000000000000000^16 ≤ 38311417755097995799^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15793 20000 38311417755097995799 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15793/20000 : ℝ)) (X := (38311417755097995799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (138311417755097995799/100000000000000000000 : ℝ) ≤ (86648836122097/80000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (138311417755097995799/100000000000000000000 : ℝ)^16 ≤ (86648836122097/80000000000000 : ℝ)^65 := by
      have hnat : (138311417755097995799 : ℕ)^16*80000000000000^65 ≤ 86648836122097^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        138311417755097995799 100000000000000000000 86648836122097 80000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (86648836122097/80000000000000 : ℝ)) (X := (138311417755097995799/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (88311417755097995799/50000000000000000000 : ℝ) ≤ (2875752735891009/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (88311417755097995799/50000000000000000000 : ℝ)^16 ≤ (2875752735891009/2500000000000000 : ℝ)^65 := by
      have hnat : (88311417755097995799 : ℕ)^16*2500000000000000^65 ≤ 2875752735891009^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88311417755097995799 50000000000000000000 2875752735891009 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2875752735891009/2500000000000000 : ℝ)) (X := (88311417755097995799/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6648836122097/63172000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(671906428301911/7896500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (15793/20000 : ℝ)) (alpha := (6648836122097/63172000000000 : ℝ)) (beta := (671906428301911/7896500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15793/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6648836122097/63172000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(671906428301911/7896500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1594948549/10000000000 : ℝ)*X 0 0+(5964299331/10000000000 : ℝ)*X 0 1+(1014282747/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4903895899/10000000000 : ℝ)*X 2 0+(6150733171/10000000000 : ℝ)*X 2 1+(-77496229/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-931162547/5000000000 : ℝ)*X 0 0+(789522491/2000000000 : ℝ)*X 0 1+(54345657/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((637639373/2000000000 : ℝ)*X 1 0+(42501/2000000000 : ℝ)*X 1 1+(258918909/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1593395517/5000000000 : ℝ)*X 2 0+(3937329341/5000000000 : ℝ)*X 2 1+(-526437353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((4519167979/10000000000 : ℝ)*X 0 0+(6634236259/10000000000 : ℝ)*X 0 1+(665757451/5000000000 : ℝ)*X 0 2+(4519167979/10000000000 : ℝ)*X 1 0+(6634236259/10000000000 : ℝ)*X 1 1+(665757451/5000000000 : ℝ)*X 1 2+(4519167979/10000000000 : ℝ)*X 2 0+(6634236259/10000000000 : ℝ)*X 2 1+(665757451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-752110951/10000000000 : ℝ)*X 0 0+(215550007/500000000 : ℝ)*X 0 1+(1425690887/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((326571491/1250000000 : ℝ)*X 1 0+(-141263817/5000000000 : ℝ)*X 1 1+(431072311/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((6952902243/10000000000 : ℝ)*X 2 0+(2266017787/5000000000 : ℝ)*X 2 1+(-90223389/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((2120796443/2500000000 : ℝ)*X 0 0+(1209509851/5000000000 : ℝ)*X 0 1+(922659353/10000000000 : ℝ)*X 0 2+(2120796443/2500000000 : ℝ)*X 1 0+(1209509851/5000000000 : ℝ)*X 1 1+(922659353/10000000000 : ℝ)*X 1 2+(2120796443/2500000000 : ℝ)*X 2 0+(1209509851/5000000000 : ℝ)*X 2 1+(922659353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-1007309857/10000000000 : ℝ)*X 0 0+(3857381377/5000000000 : ℝ)*X 0 1+(3428992567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6984090147/10000000000 : ℝ)*X 1 0+(-36919/9765625 : ℝ)*X 1 1+(957799823/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((2388107319/10000000000 : ℝ)*X 2 0+(813216773/1000000000 : ℝ)*X 2 1+(-160749979/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((1033791789/1250000000 : ℝ)*X 0 0+(2183503653/10000000000 : ℝ)*X 0 1+(801385623/5000000000 : ℝ)*X 0 2+(1033791789/1250000000 : ℝ)*X 1 0+(2183503653/10000000000 : ℝ)*X 1 1+(801385623/5000000000 : ℝ)*X 1 2+(1033791789/1250000000 : ℝ)*X 2 0+(2183503653/10000000000 : ℝ)*X 2 1+(801385623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((71553/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71553/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28171427184683131972037978459/2323407804865000000000000000000000 : ℝ) := by norm_num
    linear_combination (317987848409/500000000000 : ℝ)*(base7) + (85027/40000000000 : ℝ)*(base49) + (82093/40000000000 : ℝ)*(base53) + (226217/250000000000 : ℝ)*(base60) + (58058149139/25000000000 : ℝ)*(major_s4_0) + (58058149139/25000000000 : ℝ)*(major_s4_1) + (464464782647/200000000000 : ℝ)*(major_s4_2) + (23408819/1000000000000 : ℝ)*(sp_s4_0) + (2698190596423/1000000000000 : ℝ)*(sp_s4_7) + (2698247144467/1000000000000 : ℝ)*(sp_s4_8) + (1349114725089/500000000000 : ℝ)*(sp_s4_9) + (2192807476371/1000000000000 : ℝ)*(sp_s4_13) + (1325569/40000000000 : ℝ)*(sp_s4_14) + (9873307/500000000000 : ℝ)*(sp_s4_23) + (1556831779553/1000000000000 : ℝ)*(f.failure) + (337281149599/125000000000 : ℝ)*(f.sum) + (602763581885084481/830901316000000000000000000000 : ℝ)*base63 + (44268319525573/1579300000000000000000000000 : ℝ)*base64 + (36053425776329/78918000000000000000000000 : ℝ)*base67 + (201654947568871/315860000000000000000000000 : ℝ)*base69 + (902247704750778511/31796046900000000000000000000000 : ℝ)*base71 + (2293111435211/20133000000000000000000000 : ℝ)*base73 + (47741214661797/131530000000000000000000000 : ℝ)*base75 + (4246095586357/12583125000000000000000000 : ℝ)*base77 + (524963535847835797/1324046745000000000000000000000 : ℝ)*base79 + (7899/10000000000000000 : ℝ)*base86 + (7899/10000000000000000 : ℝ)*base88 + (7899/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70573/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70573/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4527416308475805542365921558489/464681560973000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68144167919/125000000000 : ℝ)*(base7) + (320021/500000000000 : ℝ)*(base40) + (138999/500000000000 : ℝ)*(base59) + (1983415257057/1000000000000 : ℝ)*(major_s4_0) + (1983415257057/1000000000000 : ℝ)*(major_s4_1) + (1983415257057/1000000000000 : ℝ)*(major_s4_2) + (21954049/1000000000000 : ℝ)*(sp_s4_0) + (24186581/1000000000000 : ℝ)*(sp_s4_2) + (2684913/15625000000 : ℝ)*(sp_s4_8) + (2303237484917/1000000000000 : ℝ)*(sp_s4_14) + (1151543802267/500000000000 : ℝ)*(sp_s4_15) + (1151617626193/500000000000 : ℝ)*(sp_s4_16) + (468686772321/250000000000 : ℝ)*(sp_s4_20) + (20200527/500000000000 : ℝ)*(sp_s4_27) + (265926829397/200000000000 : ℝ)*(f.failure) + (2303259438967/1000000000000 : ℝ)*(f.sum) + (4413660463996122083/5193133225000000000000000000000 : ℝ)*base62 + (1996182472943923/7896500000000000000000000000 : ℝ)*base64 + (293710372048587/1315300000000000000000000000 : ℝ)*base67 + (208542980191563/315860000000000000000000000 : ℝ)*base68 + (108178198026457245107/211973646000000000000000000000000 : ℝ)*base70 + (112641155232383/335550000000000000000000000 : ℝ)*base73 + (1342808019625399/1315300000000000000000000000 : ℝ)*base74 + (1403881582288483/2684400000000000000000000000 : ℝ)*base76 + (3493443555268477/70615826400000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1049/2000000000000000 : ℝ)*base87 + (1049/2000000000000000 : ℝ)*base89 + (1049/2000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71657/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71657/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1081043360145148424330881/63049845000000000000000000000 : ℝ) := by norm_num
    linear_combination (41600226767/62500000000 : ℝ)*(base7) + (49023/500000000000 : ℝ)*(base34) + (5119829321/125000000000 : ℝ)*(base40) + (5277317/1000000000000 : ℝ)*(base43) + (277869/500000000000 : ℝ)*(base59) + (971795284057/500000000000 : ℝ)*(major_s4_0) + (1943585388843/1000000000000 : ℝ)*(major_s4_1) + (24294883327/12500000000 : ℝ)*(major_s4_2) + (59290401/500000000000 : ℝ)*(sp_s4_9) + (19092521/500000000000 : ℝ)*(sp_s4_20) + (435303609071/200000000000 : ℝ)*(sp_s4_21) + (2176523420717/1000000000000 : ℝ)*(sp_s4_22) + (2176399562599/1000000000000 : ℝ)*(sp_s4_23) + (1968502038997/1000000000000 : ℝ)*(sp_s4_27) + (325734173453/250000000000 : ℝ)*(f.failure) + (2176523420717/1000000000000 : ℝ)*(f.sum) + (571677164966843519/2967504700000000000000000000000 : ℝ)*base62 + (68530822659999/789650000000000000000000000 : ℝ)*base64 + (6380782598749/187900000000000000000000000 : ℝ)*base67 + (4215830869409/157930000000000000000000000 : ℝ)*base69 + (2013999624227150407/12718418760000000000000000000000 : ℝ)*base71 + (510079361058763/1006650000000000000000000000 : ℝ)*base73 + (47554088321343/187900000000000000000000000 : ℝ)*base74 + (3709008539963989/4026600000000000000000000000 : ℝ)*base76 + (1320963464687972471/3782990700000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (1599/2500000000000000 : ℝ)*base86 + (1599/2500000000000000 : ℝ)*base88 + (1599/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((20133/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20133/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39459/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39459/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15793/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15793/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((71553/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71553/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70573/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70573/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71657/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71657/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302055_s4 p hpa hpb X hX hprev3

#print axioms solution
