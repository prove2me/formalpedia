-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308086_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:40:32.061407+00:00
-- url     : https://prove2.me/submissions/e40a545b-0fbd-4b2c-824a-8a2c4491c4d5

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
theorem collision_support_c308086_s3_s3_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-894755111/10000000000 : ℝ)*x 0 + (-577950681/1000000000 : ℝ)*x 1 + (2786073681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894755111/10000000000 : ℝ)^69 ≤ (86351030199/2000000000000 : ℝ)^53 := by
    have hnat : (894755111 : ℕ)^69*2000000000000^53 ≤ 86351030199^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894755111 10000000000 86351030199 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (577950681/1000000000 : ℝ)^69 ≤ (12244717213479/25000000000000 : ℝ)^53 := by
    have hnat : (577950681 : ℕ)^69*25000000000000^53 ≤ 12244717213479^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577950681 1000000000 12244717213479 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2786073681/5000000000 : ℝ)^69 ≤ (1868143185281/4000000000000 : ℝ)^53 := by
    have hnat : (2786073681 : ℕ)^69*4000000000000^53 ≤ 1868143185281^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2786073681 5000000000 1868143185281 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894755111/10000000000 : ℝ), (-577950681/1000000000 : ℝ), (2786073681/5000000000 : ℝ)] ![(86351030199/2000000000000 : ℝ), (12244717213479/25000000000000 : ℝ), (1868143185281/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894755111/10000000000 : ℝ)|^69 ≤ (86351030199/2000000000000 : ℝ)^53
        have hw : |(-894755111/10000000000 : ℝ)|=(894755111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-577950681/1000000000 : ℝ)|^69 ≤ (12244717213479/25000000000000 : ℝ)^53
        have hw : |(-577950681/1000000000 : ℝ)|=(577950681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2786073681/5000000000 : ℝ)|^69 ≤ (1868143185281/4000000000000 : ℝ)^53
        have hw : |(2786073681/5000000000 : ℝ)|=(2786073681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5625408769/10000000000 : ℝ)*x 0 + (-743252137/2000000000 : ℝ)*x 1 + (-692774489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5625408769/10000000000 : ℝ)^69 ≤ (23642800005213/50000000000000 : ℝ)^53 := by
    have hnat : (5625408769 : ℕ)^69*50000000000000^53 ≤ 23642800005213^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625408769 10000000000 23642800005213 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743252137/2000000000 : ℝ)^69 ≤ (27563026442437/100000000000000 : ℝ)^53 := by
    have hnat : (743252137 : ℕ)^69*100000000000000^53 ≤ 27563026442437^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743252137 2000000000 27563026442437 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (692774489/2000000000 : ℝ)^69 ≤ (12575686766987/50000000000000 : ℝ)^53 := by
    have hnat : (692774489 : ℕ)^69*50000000000000^53 ≤ 12575686766987^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692774489 2000000000 12575686766987 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5625408769/10000000000 : ℝ), (-743252137/2000000000 : ℝ), (-692774489/2000000000 : ℝ)] ![(23642800005213/50000000000000 : ℝ), (27563026442437/100000000000000 : ℝ), (12575686766987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5625408769/10000000000 : ℝ)|^69 ≤ (23642800005213/50000000000000 : ℝ)^53
        have hw : |(5625408769/10000000000 : ℝ)|=(5625408769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-743252137/2000000000 : ℝ)|^69 ≤ (27563026442437/100000000000000 : ℝ)^53
        have hw : |(-743252137/2000000000 : ℝ)|=(743252137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-692774489/2000000000 : ℝ)|^69 ≤ (12575686766987/50000000000000 : ℝ)^53
        have hw : |(-692774489/2000000000 : ℝ)|=(692774489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-176963189/2500000000 : ℝ)*x 0 + (-3362537853/5000000000 : ℝ)*x 1 + (1168662673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176963189/2500000000 : ℝ)^69 ≤ (198900513273/6250000000000 : ℝ)^53 := by
    have hnat : (176963189 : ℕ)^69*6250000000000^53 ≤ 198900513273^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176963189 2500000000 198900513273 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3362537853/5000000000 : ℝ)^69 ≤ (7457465352807/12500000000000 : ℝ)^53 := by
    have hnat : (3362537853 : ℕ)^69*12500000000000^53 ≤ 7457465352807^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362537853 5000000000 7457465352807 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1168662673/2500000000 : ℝ)^69 ≤ (7431573790699/20000000000000 : ℝ)^53 := by
    have hnat : (1168662673 : ℕ)^69*20000000000000^53 ≤ 7431573790699^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168662673 2500000000 7431573790699 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176963189/2500000000 : ℝ), (-3362537853/5000000000 : ℝ), (1168662673/2500000000 : ℝ)] ![(198900513273/6250000000000 : ℝ), (7457465352807/12500000000000 : ℝ), (7431573790699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176963189/2500000000 : ℝ)|^69 ≤ (198900513273/6250000000000 : ℝ)^53
        have hw : |(-176963189/2500000000 : ℝ)|=(176963189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3362537853/5000000000 : ℝ)|^69 ≤ (7457465352807/12500000000000 : ℝ)^53
        have hw : |(-3362537853/5000000000 : ℝ)|=(3362537853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1168662673/2500000000 : ℝ)|^69 ≤ (7431573790699/20000000000000 : ℝ)^53
        have hw : |(1168662673/2500000000 : ℝ)|=(1168662673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1471204377/2500000000 : ℝ)*x 0 + (3469508959/10000000000 : ℝ)*x 1 + (3410858797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1471204377/2500000000 : ℝ)^69 ≤ (12535984375243/25000000000000 : ℝ)^53 := by
    have hnat : (1471204377 : ℕ)^69*25000000000000^53 ≤ 12535984375243^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471204377 2500000000 12535984375243 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3469508959/10000000000 : ℝ)^69 ≤ (12602334498831/50000000000000 : ℝ)^53 := by
    have hnat : (3469508959 : ℕ)^69*50000000000000^53 ≤ 12602334498831^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3469508959 10000000000 12602334498831 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3410858797/10000000000 : ℝ)^69 ≤ (24651393482357/100000000000000 : ℝ)^53 := by
    have hnat : (3410858797 : ℕ)^69*100000000000000^53 ≤ 24651393482357^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410858797 10000000000 24651393482357 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1471204377/2500000000 : ℝ), (3469508959/10000000000 : ℝ), (3410858797/10000000000 : ℝ)] ![(12535984375243/25000000000000 : ℝ), (12602334498831/50000000000000 : ℝ), (24651393482357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1471204377/2500000000 : ℝ)|^69 ≤ (12535984375243/25000000000000 : ℝ)^53
        have hw : |(1471204377/2500000000 : ℝ)|=(1471204377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3469508959/10000000000 : ℝ)|^69 ≤ (12602334498831/50000000000000 : ℝ)^53
        have hw : |(3469508959/10000000000 : ℝ)|=(3469508959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3410858797/10000000000 : ℝ)|^69 ≤ (24651393482357/100000000000000 : ℝ)^53
        have hw : |(3410858797/10000000000 : ℝ)|=(3410858797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5899037527/10000000000 : ℝ)*x 0 + (-3473795757/10000000000 : ℝ)*x 1 + (-677951613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5899037527/10000000000 : ℝ)^69 ≤ (50301741177647/100000000000000 : ℝ)^53 := by
    have hnat : (5899037527 : ℕ)^69*100000000000000^53 ≤ 50301741177647^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5899037527 10000000000 50301741177647 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3473795757/10000000000 : ℝ)^69 ≤ (25245219869027/100000000000000 : ℝ)^53 := by
    have hnat : (3473795757 : ℕ)^69*100000000000000^53 ≤ 25245219869027^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473795757 10000000000 25245219869027 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677951613/2000000000 : ℝ)^69 ≤ (24453038934769/100000000000000 : ℝ)^53 := by
    have hnat : (677951613 : ℕ)^69*100000000000000^53 ≤ 24453038934769^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677951613 2000000000 24453038934769 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5899037527/10000000000 : ℝ), (-3473795757/10000000000 : ℝ), (-677951613/2000000000 : ℝ)] ![(50301741177647/100000000000000 : ℝ), (25245219869027/100000000000000 : ℝ), (24453038934769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5899037527/10000000000 : ℝ)|^69 ≤ (50301741177647/100000000000000 : ℝ)^53
        have hw : |(5899037527/10000000000 : ℝ)|=(5899037527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3473795757/10000000000 : ℝ)|^69 ≤ (25245219869027/100000000000000 : ℝ)^53
        have hw : |(-3473795757/10000000000 : ℝ)|=(3473795757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-677951613/2000000000 : ℝ)|^69 ≤ (24453038934769/100000000000000 : ℝ)^53
        have hw : |(-677951613/2000000000 : ℝ)|=(677951613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (216731111/625000000 : ℝ)*x 0 + (-1085434191/5000000000 : ℝ)*x 1 + (3425727957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216731111/625000000 : ℝ)^69 ≤ (6296885173903/25000000000000 : ℝ)^53 := by
    have hnat : (216731111 : ℕ)^69*25000000000000^53 ≤ 6296885173903^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216731111 625000000 6296885173903 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085434191/5000000000 : ℝ)^69 ≤ (2737801153107/20000000000000 : ℝ)^53 := by
    have hnat : (1085434191 : ℕ)^69*20000000000000^53 ≤ 2737801153107^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085434191 5000000000 2737801153107 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3425727957/5000000000 : ℝ)^69 ≤ (2444938140777/4000000000000 : ℝ)^53 := by
    have hnat : (3425727957 : ℕ)^69*4000000000000^53 ≤ 2444938140777^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3425727957 5000000000 2444938140777 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216731111/625000000 : ℝ), (-1085434191/5000000000 : ℝ), (3425727957/5000000000 : ℝ)] ![(6296885173903/25000000000000 : ℝ), (2737801153107/20000000000000 : ℝ), (2444938140777/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216731111/625000000 : ℝ)|^69 ≤ (6296885173903/25000000000000 : ℝ)^53
        have hw : |(216731111/625000000 : ℝ)|=(216731111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085434191/5000000000 : ℝ)|^69 ≤ (2737801153107/20000000000000 : ℝ)^53
        have hw : |(-1085434191/5000000000 : ℝ)|=(1085434191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3425727957/5000000000 : ℝ)|^69 ≤ (2444938140777/4000000000000 : ℝ)^53
        have hw : |(3425727957/5000000000 : ℝ)|=(3425727957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-53423359/2000000000 : ℝ)*x 0 + (-1382177827/2500000000 : ℝ)*x 1 + (6129487799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53423359/2000000000 : ℝ)^69 ≤ (89483521217/10000000000000 : ℝ)^53 := by
    have hnat : (53423359 : ℕ)^69*10000000000000^53 ≤ 89483521217^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53423359 2000000000 89483521217 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382177827/2500000000 : ℝ)^69 ≤ (23115084001089/50000000000000 : ℝ)^53 := by
    have hnat : (1382177827 : ℕ)^69*50000000000000^53 ≤ 23115084001089^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382177827 2500000000 23115084001089 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6129487799/10000000000 : ℝ)^69 ≤ (3304687298681/6250000000000 : ℝ)^53 := by
    have hnat : (6129487799 : ℕ)^69*6250000000000^53 ≤ 3304687298681^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6129487799 10000000000 3304687298681 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53423359/2000000000 : ℝ), (-1382177827/2500000000 : ℝ), (6129487799/10000000000 : ℝ)] ![(89483521217/10000000000000 : ℝ), (23115084001089/50000000000000 : ℝ), (3304687298681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53423359/2000000000 : ℝ)|^69 ≤ (89483521217/10000000000000 : ℝ)^53
        have hw : |(-53423359/2000000000 : ℝ)|=(53423359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382177827/2500000000 : ℝ)|^69 ≤ (23115084001089/50000000000000 : ℝ)^53
        have hw : |(-1382177827/2500000000 : ℝ)|=(1382177827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6129487799/10000000000 : ℝ)|^69 ≤ (3304687298681/6250000000000 : ℝ)^53
        have hw : |(6129487799/10000000000 : ℝ)|=(6129487799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6610071647/10000000000 : ℝ)*x 0 + (823539407/2500000000 : ℝ)*x 1 + (2691049947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6610071647/10000000000 : ℝ)^69 ≤ (2333397749121/4000000000000 : ℝ)^53 := by
    have hnat : (6610071647 : ℕ)^69*4000000000000^53 ≤ 2333397749121^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6610071647 10000000000 2333397749121 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823539407/2500000000 : ℝ)^69 ≤ (23559049972803/100000000000000 : ℝ)^53 := by
    have hnat : (823539407 : ℕ)^69*100000000000000^53 ≤ 23559049972803^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823539407 2500000000 23559049972803 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2691049947/10000000000 : ℝ)^69 ≤ (1810600628373/10000000000000 : ℝ)^53 := by
    have hnat : (2691049947 : ℕ)^69*10000000000000^53 ≤ 1810600628373^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691049947 10000000000 1810600628373 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6610071647/10000000000 : ℝ), (823539407/2500000000 : ℝ), (2691049947/10000000000 : ℝ)] ![(2333397749121/4000000000000 : ℝ), (23559049972803/100000000000000 : ℝ), (1810600628373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6610071647/10000000000 : ℝ)|^69 ≤ (2333397749121/4000000000000 : ℝ)^53
        have hw : |(6610071647/10000000000 : ℝ)|=(6610071647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(823539407/2500000000 : ℝ)|^69 ≤ (23559049972803/100000000000000 : ℝ)^53
        have hw : |(823539407/2500000000 : ℝ)|=(823539407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2691049947/10000000000 : ℝ)|^69 ≤ (1810600628373/10000000000000 : ℝ)^53
        have hw : |(2691049947/10000000000 : ℝ)|=(2691049947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6117130221/10000000000 : ℝ)*x 0 + (-370391289/1000000000 : ℝ)*x 1 + (-1442321883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6117130221/10000000000 : ℝ)^69 ≤ (6592032144647/12500000000000 : ℝ)^53 := by
    have hnat : (6117130221 : ℕ)^69*12500000000000^53 ≤ 6592032144647^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6117130221 10000000000 6592032144647 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370391289/1000000000 : ℝ)^69 ≤ (3430482110597/12500000000000 : ℝ)^53 := by
    have hnat : (370391289 : ℕ)^69*12500000000000^53 ≤ 3430482110597^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370391289 1000000000 3430482110597 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1442321883/5000000000 : ℝ)^69 ≤ (19819885941421/100000000000000 : ℝ)^53 := by
    have hnat : (1442321883 : ℕ)^69*100000000000000^53 ≤ 19819885941421^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442321883 5000000000 19819885941421 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6117130221/10000000000 : ℝ), (-370391289/1000000000 : ℝ), (-1442321883/5000000000 : ℝ)] ![(6592032144647/12500000000000 : ℝ), (3430482110597/12500000000000 : ℝ), (19819885941421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6117130221/10000000000 : ℝ)|^69 ≤ (6592032144647/12500000000000 : ℝ)^53
        have hw : |(6117130221/10000000000 : ℝ)|=(6117130221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370391289/1000000000 : ℝ)|^69 ≤ (3430482110597/12500000000000 : ℝ)^53
        have hw : |(-370391289/1000000000 : ℝ)|=(370391289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1442321883/5000000000 : ℝ)|^69 ≤ (19819885941421/100000000000000 : ℝ)^53
        have hw : |(-1442321883/5000000000 : ℝ)|=(1442321883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1804732501/5000000000 : ℝ)*x 0 + (-669067311/2500000000 : ℝ)*x 1 + (6360766357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1804732501/5000000000 : ℝ)^69 ≤ (26536318566121/100000000000000 : ℝ)^53 := by
    have hnat : (1804732501 : ℕ)^69*100000000000000^53 ≤ 26536318566121^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804732501 5000000000 26536318566121 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669067311/2500000000 : ℝ)^69 ≤ (4494160934653/25000000000000 : ℝ)^53 := by
    have hnat : (669067311 : ℕ)^69*25000000000000^53 ≤ 4494160934653^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669067311 2500000000 4494160934653 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6360766357/10000000000 : ℝ)^69 ≤ (27743518842747/50000000000000 : ℝ)^53 := by
    have hnat : (6360766357 : ℕ)^69*50000000000000^53 ≤ 27743518842747^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6360766357 10000000000 27743518842747 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1804732501/5000000000 : ℝ), (-669067311/2500000000 : ℝ), (6360766357/10000000000 : ℝ)] ![(26536318566121/100000000000000 : ℝ), (4494160934653/25000000000000 : ℝ), (27743518842747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1804732501/5000000000 : ℝ)|^69 ≤ (26536318566121/100000000000000 : ℝ)^53
        have hw : |(1804732501/5000000000 : ℝ)|=(1804732501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-669067311/2500000000 : ℝ)|^69 ≤ (4494160934653/25000000000000 : ℝ)^53
        have hw : |(-669067311/2500000000 : ℝ)|=(669067311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6360766357/10000000000 : ℝ)|^69 ≤ (27743518842747/50000000000000 : ℝ)^53
        have hw : |(6360766357/10000000000 : ℝ)|=(6360766357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-206886519/10000000000 : ℝ)*x 0 + (-160174927/250000000 : ℝ)*x 1 + (5261780953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206886519/10000000000 : ℝ)^69 ≤ (641614228457/100000000000000 : ℝ)^53 := by
    have hnat : (206886519 : ℕ)^69*100000000000000^53 ≤ 641614228457^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206886519 10000000000 641614228457 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160174927/250000000 : ℝ)^69 ≤ (28006322494691/50000000000000 : ℝ)^53 := by
    have hnat : (160174927 : ℕ)^69*50000000000000^53 ≤ 28006322494691^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160174927 250000000 28006322494691 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261780953/10000000000 : ℝ)^69 ≤ (43345740763029/100000000000000 : ℝ)^53 := by
    have hnat : (5261780953 : ℕ)^69*100000000000000^53 ≤ 43345740763029^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261780953 10000000000 43345740763029 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206886519/10000000000 : ℝ), (-160174927/250000000 : ℝ), (5261780953/10000000000 : ℝ)] ![(641614228457/100000000000000 : ℝ), (28006322494691/50000000000000 : ℝ), (43345740763029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206886519/10000000000 : ℝ)|^69 ≤ (641614228457/100000000000000 : ℝ)^53
        have hw : |(-206886519/10000000000 : ℝ)|=(206886519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-160174927/250000000 : ℝ)|^69 ≤ (28006322494691/50000000000000 : ℝ)^53
        have hw : |(-160174927/250000000 : ℝ)|=(160174927/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261780953/10000000000 : ℝ)|^69 ≤ (43345740763029/100000000000000 : ℝ)^53
        have hw : |(5261780953/10000000000 : ℝ)|=(5261780953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6670301869/10000000000 : ℝ)*x 0 + (3063381731/10000000000 : ℝ)*x 1 + (356643951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6670301869/10000000000 : ℝ)^69 ≤ (59027900192659/100000000000000 : ℝ)^53 := by
    have hnat : (6670301869 : ℕ)^69*100000000000000^53 ≤ 59027900192659^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6670301869 10000000000 59027900192659 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3063381731/10000000000 : ℝ)^69 ≤ (5358361752731/25000000000000 : ℝ)^53 := by
    have hnat : (3063381731 : ℕ)^69*25000000000000^53 ≤ 5358361752731^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3063381731 10000000000 5358361752731 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356643951/1250000000 : ℝ)^69 ≤ (1953865278431/10000000000000 : ℝ)^53 := by
    have hnat : (356643951 : ℕ)^69*10000000000000^53 ≤ 1953865278431^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356643951 1250000000 1953865278431 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6670301869/10000000000 : ℝ), (3063381731/10000000000 : ℝ), (356643951/1250000000 : ℝ)] ![(59027900192659/100000000000000 : ℝ), (5358361752731/25000000000000 : ℝ), (1953865278431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6670301869/10000000000 : ℝ)|^69 ≤ (59027900192659/100000000000000 : ℝ)^53
        have hw : |(6670301869/10000000000 : ℝ)|=(6670301869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3063381731/10000000000 : ℝ)|^69 ≤ (5358361752731/25000000000000 : ℝ)^53
        have hw : |(3063381731/10000000000 : ℝ)|=(3063381731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356643951/1250000000 : ℝ)|^69 ≤ (1953865278431/10000000000000 : ℝ)^53
        have hw : |(356643951/1250000000 : ℝ)|=(356643951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5391544161/10000000000 : ℝ)*x 0 + (-1939961671/5000000000 : ℝ)*x 1 + (-178208923/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391544161/10000000000 : ℝ)^69 ≤ (11185642216967/25000000000000 : ℝ)^53 := by
    have hnat : (5391544161 : ℕ)^69*25000000000000^53 ≤ 11185642216967^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391544161 10000000000 11185642216967 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939961671/5000000000 : ℝ)^69 ≤ (29153740461057/100000000000000 : ℝ)^53 := by
    have hnat : (1939961671 : ℕ)^69*100000000000000^53 ≤ 29153740461057^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939961671 5000000000 29153740461057 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178208923/500000000 : ℝ)^69 ≤ (13051845324501/50000000000000 : ℝ)^53 := by
    have hnat : (178208923 : ℕ)^69*50000000000000^53 ≤ 13051845324501^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178208923 500000000 13051845324501 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391544161/10000000000 : ℝ), (-1939961671/5000000000 : ℝ), (-178208923/500000000 : ℝ)] ![(11185642216967/25000000000000 : ℝ), (29153740461057/100000000000000 : ℝ), (13051845324501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391544161/10000000000 : ℝ)|^69 ≤ (11185642216967/25000000000000 : ℝ)^53
        have hw : |(5391544161/10000000000 : ℝ)|=(5391544161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1939961671/5000000000 : ℝ)|^69 ≤ (29153740461057/100000000000000 : ℝ)^53
        have hw : |(-1939961671/5000000000 : ℝ)|=(1939961671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178208923/500000000 : ℝ)|^69 ≤ (13051845324501/50000000000000 : ℝ)^53
        have hw : |(-178208923/500000000 : ℝ)|=(178208923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308086_s3_s3_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5158024951/10000000000 : ℝ)*x 0 + (-2849719283/10000000000 : ℝ)*x 1 + (2390185801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5158024951/10000000000 : ℝ)^69 ≤ (42236311686949/100000000000000 : ℝ)^53 := by
    have hnat : (5158024951 : ℕ)^69*100000000000000^53 ≤ 42236311686949^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158024951 10000000000 42236311686949 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2849719283/10000000000 : ℝ)^69 ≤ (3901611528079/20000000000000 : ℝ)^53 := by
    have hnat : (2849719283 : ℕ)^69*20000000000000^53 ≤ 3901611528079^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849719283 10000000000 3901611528079 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2390185801/5000000000 : ℝ)^69 ≤ (38255630652633/100000000000000 : ℝ)^53 := by
    have hnat : (2390185801 : ℕ)^69*100000000000000^53 ≤ 38255630652633^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390185801 5000000000 38255630652633 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5158024951/10000000000 : ℝ), (-2849719283/10000000000 : ℝ), (2390185801/5000000000 : ℝ)] ![(42236311686949/100000000000000 : ℝ), (3901611528079/20000000000000 : ℝ), (38255630652633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5158024951/10000000000 : ℝ)|^69 ≤ (42236311686949/100000000000000 : ℝ)^53
        have hw : |(5158024951/10000000000 : ℝ)|=(5158024951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2849719283/10000000000 : ℝ)|^69 ≤ (3901611528079/20000000000000 : ℝ)^53
        have hw : |(-2849719283/10000000000 : ℝ)|=(2849719283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2390185801/5000000000 : ℝ)|^69 ≤ (38255630652633/100000000000000 : ℝ)^53
        have hw : |(2390185801/5000000000 : ℝ)|=(2390185801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308086_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((2277/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2277/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1797/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-1797/2500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1351/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15223/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15223/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-36933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-36933/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7411/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7411/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (2277/5000 : ℝ) ^ (17/4 : ℝ) ≤ (3533217409359923211/100000000000000000000 : ℝ) := by
    have hpowers : (2277/5000 : ℝ)^17 ≤ (3533217409359923211/100000000000000000000 : ℝ)^4 := by
      have hnat : (2277 : ℕ)^17*100000000000000000000^4 ≤ 3533217409359923211^4*5000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 5000 3533217409359923211 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/5000 : ℝ)) (X := (3533217409359923211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0a : (103533217409359923211/100000000000000000000 : ℝ) ≤ (10082034219665587/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (103533217409359923211/100000000000000000000 : ℝ)^4 ≤ (10082034219665587/10000000000000000 : ℝ)^17 := by
      have hnat : (103533217409359923211 : ℕ)^4*10000000000000000^17 ≤ 10082034219665587^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103533217409359923211 100000000000000000000 10082034219665587 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10082034219665587/10000000000000000 : ℝ)) (X := (103533217409359923211/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0b : (53533217409359923211/50000000000000000000 : ℝ) ≤ (10161954752195307/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (53533217409359923211/50000000000000000000 : ℝ)^4 ≤ (10161954752195307/10000000000000000 : ℝ)^17 := by
      have hnat : (53533217409359923211 : ℕ)^4*10000000000000000^17 ≤ 10161954752195307^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53533217409359923211 50000000000000000000 10161954752195307 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10161954752195307/10000000000000000 : ℝ)) (X := (53533217409359923211/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27344739888529/1518000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1998013313243/113850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (2277/5000 : ℝ)) (alpha := (27344739888529/1518000000000000 : ℝ)) (beta := (1998013313243/113850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2277/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27344739888529/1518000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1998013313243/113850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (1797/2500 : ℝ) ^ (17/4 : ℝ) ≤ (983205461239964093/4000000000000000000 : ℝ) := by
    have hpowers : (1797/2500 : ℝ)^17 ≤ (983205461239964093/4000000000000000000 : ℝ)^4 := by
      have hnat : (1797 : ℕ)^17*4000000000000000000^4 ≤ 983205461239964093^4*2500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1797 2500 983205461239964093 4000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1797/2500 : ℝ)) (X := (983205461239964093/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1a : (4983205461239964093/4000000000000000000 : ℝ) ≤ (1316341443488781/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (4983205461239964093/4000000000000000000 : ℝ)^4 ≤ (1316341443488781/1250000000000000 : ℝ)^17 := by
      have hnat : (4983205461239964093 : ℕ)^4*1250000000000000^17 ≤ 1316341443488781^17*4000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4983205461239964093 4000000000000000000 1316341443488781 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1316341443488781/1250000000000000 : ℝ)) (X := (4983205461239964093/4000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1b : (2983205461239964093/2000000000000000000 : ℝ) ≤ (2197301058944299/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2983205461239964093/2000000000000000000 : ℝ)^4 ≤ (2197301058944299/2000000000000000 : ℝ)^17 := by
      have hnat : (2983205461239964093 : ℕ)^4*2000000000000000^17 ≤ 2197301058944299^17*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2983205461239964093 2000000000000000000 2197301058944299 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2197301058944299/2000000000000000 : ℝ)) (X := (2983205461239964093/2000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(66341443488781/898500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(455773746811247/7188000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1797/2500 : ℝ)) (alpha := (66341443488781/898500000000000 : ℝ)) (beta := (455773746811247/7188000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1797/2500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(66341443488781/898500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(455773746811247/7188000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (1351/2000 : ℝ) ^ (17/4 : ℝ) ≤ (73733998616539727/390625000000000000 : ℝ) := by
    have hpowers : (1351/2000 : ℝ)^17 ≤ (73733998616539727/390625000000000000 : ℝ)^4 := by
      have hnat : (1351 : ℕ)^17*390625000000000000^4 ≤ 73733998616539727^4*2000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1351 2000 73733998616539727 390625000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1351/2000 : ℝ)) (X := (73733998616539727/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2a : (464358998616539727/390625000000000000 : ℝ) ≤ (10415236519225807/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (464358998616539727/390625000000000000 : ℝ)^4 ≤ (10415236519225807/10000000000000000 : ℝ)^17 := by
      have hnat : (464358998616539727 : ℕ)^4*10000000000000000^17 ≤ 10415236519225807^17*390625000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        464358998616539727 390625000000000000 10415236519225807 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10415236519225807/10000000000000000 : ℝ)) (X := (464358998616539727/390625000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2b : (269046498616539727/195312500000000000 : ℝ) ≤ (2156546234193257/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (269046498616539727/195312500000000000 : ℝ)^4 ≤ (2156546234193257/2000000000000000 : ℝ)^17 := by
      have hnat : (269046498616539727 : ℕ)^4*2000000000000000^17 ≤ 2156546234193257^17*195312500000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269046498616539727 195312500000000000 2156546234193257 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2156546234193257/2000000000000000 : ℝ)) (X := (269046498616539727/195312500000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(415236519225807/6755000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(183747325870239/3377500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1351/2000 : ℝ)) (alpha := (415236519225807/6755000000000000 : ℝ)) (beta := (183747325870239/3377500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1351/2000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(415236519225807/6755000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(183747325870239/3377500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-894755111/10000000000 : ℝ)*X 0 0+(-577950681/1000000000 : ℝ)*X 0 1+(2786073681/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5625408769/10000000000 : ℝ)*X 2 0+(-743252137/2000000000 : ℝ)*X 2 1+(-692774489/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-176963189/2500000000 : ℝ)*X 0 0+(-3362537853/5000000000 : ℝ)*X 0 1+(1168662673/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((1471204377/2500000000 : ℝ)*X 1 0+(3469508959/10000000000 : ℝ)*X 1 1+(3410858797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((5899037527/10000000000 : ℝ)*X 2 0+(-3473795757/10000000000 : ℝ)*X 2 1+(-677951613/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((216731111/625000000 : ℝ)*X 0 0+(-1085434191/5000000000 : ℝ)*X 0 1+(3425727957/5000000000 : ℝ)*X 0 2+(216731111/625000000 : ℝ)*X 1 0+(-1085434191/5000000000 : ℝ)*X 1 1+(3425727957/5000000000 : ℝ)*X 1 2+(216731111/625000000 : ℝ)*X 2 0+(-1085434191/5000000000 : ℝ)*X 2 1+(3425727957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-53423359/2000000000 : ℝ)*X 0 0+(-1382177827/2500000000 : ℝ)*X 0 1+(6129487799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((6610071647/10000000000 : ℝ)*X 1 0+(823539407/2500000000 : ℝ)*X 1 1+(2691049947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((6117130221/10000000000 : ℝ)*X 2 0+(-370391289/1000000000 : ℝ)*X 2 1+(-1442321883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1804732501/5000000000 : ℝ)*X 0 0+(-669067311/2500000000 : ℝ)*X 0 1+(6360766357/10000000000 : ℝ)*X 0 2+(1804732501/5000000000 : ℝ)*X 1 0+(-669067311/2500000000 : ℝ)*X 1 1+(6360766357/10000000000 : ℝ)*X 1 2+(1804732501/5000000000 : ℝ)*X 2 0+(-669067311/2500000000 : ℝ)*X 2 1+(6360766357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-206886519/10000000000 : ℝ)*X 0 0+(-160174927/250000000 : ℝ)*X 0 1+(5261780953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6670301869/10000000000 : ℝ)*X 1 0+(3063381731/10000000000 : ℝ)*X 1 1+(356643951/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((5391544161/10000000000 : ℝ)*X 2 0+(-1939961671/5000000000 : ℝ)*X 2 1+(-178208923/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((5158024951/10000000000 : ℝ)*X 0 0+(-2849719283/10000000000 : ℝ)*X 0 1+(2390185801/5000000000 : ℝ)*X 0 2+(5158024951/10000000000 : ℝ)*X 1 0+(-2849719283/10000000000 : ℝ)*X 1 1+(2390185801/5000000000 : ℝ)*X 1 2+(5158024951/10000000000 : ℝ)*X 2 0+(-2849719283/10000000000 : ℝ)*X 2 1+(2390185801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308086_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((15223/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15223/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1177178140650919344849/253000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227522064129/500000000000 : ℝ)*(base40) + (806147/1000000000000 : ℝ)*(base50) + (484151/250000000000 : ℝ)*(base60) + (3928637856081/1000000000000 : ℝ)*(major_s3_0) + (3928637856081/1000000000000 : ℝ)*(major_s3_1) + (3928637856081/1000000000000 : ℝ)*(major_s3_2) + (110196859/1000000000000 : ℝ)*(sp_s3_2) + (668790041063/125000000000 : ℝ)*(sp_s3_7) + (2675171192411/500000000000 : ℝ)*(sp_s3_8) + (5350219319077/1000000000000 : ℝ)*(sp_s3_9) + (2506930937099/1000000000000 : ℝ)*(sp_s3_13) + (6434443/500000000000 : ℝ)*(sp_s3_16) + (10491/12500000000 : ℝ)*(sp_s3_20) + (11028159/500000000000 : ℝ)*(sp_s3_21) + (2506931776379/1000000000000 : ℝ)*(f.failure) + (2675171192411/500000000000 : ℝ)*(f.sum) + (210095066610991427/16184980000000000000000000000000 : ℝ)*base63 + (602861155952141/3377500000000000000000000000 : ℝ)*base65 + (121907314717513/299500000000000000000000000 : ℝ)*base66 + (1899722082897633/6755000000000000000000000000 : ℝ)*base68 + (993833014358317643/3418030000000000000000000000000 : ℝ)*base70 + (1134355232539/37950000000000000000000000 : ℝ)*base72 + (206727462216331/2396000000000000000000000000 : ℝ)*base74 + (23597993272517/506000000000000000000000000 : ℝ)*base76 + (6797415128531923/227320500000000000000000000000 : ℝ)*base79 + (29469/100000000000000000 : ℝ)*base87 + (29469/100000000000000000 : ℝ)*base89 + (29469/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-36933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-36933/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4885581678845765992113/844375000000000000000000000 : ℝ) := by norm_num
    linear_combination (655897/200000000000 : ℝ)*(base39) + (183707406219/125000000000 : ℝ)*(base40) + (414036079693/1000000000000 : ℝ)*(base60) + (374655183307/62500000000 : ℝ)*(major_s3_0) + (374655183307/62500000000 : ℝ)*(major_s3_1) + (374655183307/62500000000 : ℝ)*(major_s3_2) + (3281851/250000000000 : ℝ)*(sp_s3_0) + (17657427/200000000000 : ℝ)*(sp_s3_13) + (1632753510671/200000000000 : ℝ)*(sp_s3_14) + (4081841588219/500000000000 : ℝ)*(sp_s3_15) + (4081890340379/500000000000 : ℝ)*(sp_s3_16) + (47813490871/12500000000 : ℝ)*(sp_s3_20) + (97504321/1000000000000 : ℝ)*(sp_s3_22) + (15699569/1000000000000 : ℝ)*(sp_s3_27) + (59768488381/15625000000 : ℝ)*(f.failure) + (4081890340379/500000000000 : ℝ)*(f.sum) + (261110683308811043/3034683750000000000000000000000 : ℝ)*base62 + (508274506177891/1688750000000000000000000000 : ℝ)*base65 + (173440593396289/449250000000000000000000000 : ℝ)*base66 + (536122105084627/844375000000000000000000000 : ℝ)*base68 + (72107436735160769/320440312500000000000000000000 : ℝ)*base70 + (2573842367777/56925000000000000000000000 : ℝ)*base72 + (16363279761401/112312500000000000000000000 : ℝ)*base75 + (9673582595381/189750000000000000000000000 : ℝ)*base77 + (7173136021185911/85245187500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (109/1562500000000000 : ℝ)*base86 + (109/1562500000000000 : ℝ)*base88 + (109/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7411/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7411/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (130885985915335851073897497/29248571000000000000000000000000 : ℝ) := by norm_num
    linear_combination (970961/500000000000 : ℝ)*(base39) + (771604764527/500000000000 : ℝ)*(base40) + (2839486771611/500000000000 : ℝ)*(major_s3_0) + (2839486771611/500000000000 : ℝ)*(major_s3_1) + (2839486771611/500000000000 : ℝ)*(major_s3_2) + (22947/250000000000 : ℝ)*(sp_s3_0) + (6620893/1000000000000 : ℝ)*(sp_s3_2) + (27940569/1000000000000 : ℝ)*(sp_s3_7) + (42850909/1000000000000 : ℝ)*(sp_s3_15) + (5302349/500000000000 : ℝ)*(sp_s3_16) + (966758288189/125000000000 : ℝ)*(sp_s3_21) + (7734051486959/1000000000000 : ℝ)*(sp_s3_22) + (3867038556139/500000000000 : ℝ)*(sp_s3_23) + (3623851256913/1000000000000 : ℝ)*(sp_s3_27) + (3623851256913/1000000000000 : ℝ)*(f.failure) + (7734094337869/1000000000000 : ℝ)*(f.sum) + (340228961943226991/1156070000000000000000000000000 : ℝ)*base63 + (44804058651761/120625000000000000000000000 : ℝ)*base64 + (69153477889547/149750000000000000000000000 : ℝ)*base67 + (540129513319761/482500000000000000000000000 : ℝ)*base69 + (9086997242451319/244145000000000000000000000000 : ℝ)*base70 + (11115061821929/12650000000000000000000000 : ℝ)*base73 + (578965605648839/1198000000000000000000000000 : ℝ)*base75 + (133693989635927/253000000000000000000000000 : ℝ)*base76 + (1995491777365087/4735843750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (106857/100000000000000000 : ℝ)*base86 + (106857/100000000000000000 : ℝ)*base88 + (106857/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((2277/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2277/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1797/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-1797/2500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1351/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15223/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15223/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-36933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-36933/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7411/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7411/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308086_s3 p hpa hpb X hX hprev2

#print axioms solution
