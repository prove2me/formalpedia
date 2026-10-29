-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308053_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:21.686003+00:00
-- url     : https://prove2.me/submissions/dc2c4128-cae4-4ab6-9428-7e0f9483b2f7

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
theorem collision_support_c308053_s5_s5_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2780858823/10000000000 : ℝ)*x 0 + (1249183293/2500000000 : ℝ)*x 1 + (5001780639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2780858823/10000000000 : ℝ)^69 ≤ (18896610215053/100000000000000 : ℝ)^53 := by
    have hnat : (2780858823 : ℕ)^69*100000000000000^53 ≤ 18896610215053^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780858823 10000000000 18896610215053 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249183293/2500000000 : ℝ)^69 ≤ (20262521736083/50000000000000 : ℝ)^53 := by
    have hnat : (1249183293 : ℕ)^69*50000000000000^53 ≤ 20262521736083^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249183293 2500000000 20262521736083 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5001780639/10000000000 : ℝ)^69 ≤ (40578346298673/100000000000000 : ℝ)^53 := by
    have hnat : (5001780639 : ℕ)^69*100000000000000^53 ≤ 40578346298673^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001780639 10000000000 40578346298673 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2780858823/10000000000 : ℝ), (1249183293/2500000000 : ℝ), (5001780639/10000000000 : ℝ)] ![(18896610215053/100000000000000 : ℝ), (20262521736083/50000000000000 : ℝ), (40578346298673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2780858823/10000000000 : ℝ)|^69 ≤ (18896610215053/100000000000000 : ℝ)^53
        have hw : |(-2780858823/10000000000 : ℝ)|=(2780858823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249183293/2500000000 : ℝ)|^69 ≤ (20262521736083/50000000000000 : ℝ)^53
        have hw : |(1249183293/2500000000 : ℝ)|=(1249183293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5001780639/10000000000 : ℝ)|^69 ≤ (40578346298673/100000000000000 : ℝ)^53
        have hw : |(5001780639/10000000000 : ℝ)|=(5001780639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1124018249/2500000000 : ℝ)*x 0 + (-2305433583/10000000000 : ℝ)*x 1 + (5860602591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124018249/2500000000 : ℝ)^69 ≤ (275942350057/781250000000 : ℝ)^53 := by
    have hnat : (1124018249 : ℕ)^69*781250000000^53 ≤ 275942350057^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124018249 2500000000 275942350057 781250000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305433583/10000000000 : ℝ)^69 ≤ (7401948353713/50000000000000 : ℝ)^53 := by
    have hnat : (2305433583 : ℕ)^69*50000000000000^53 ≤ 7401948353713^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305433583 10000000000 7401948353713 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5860602591/10000000000 : ℝ)^69 ≤ (6234435308139/12500000000000 : ℝ)^53 := by
    have hnat : (5860602591 : ℕ)^69*12500000000000^53 ≤ 6234435308139^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5860602591 10000000000 6234435308139 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124018249/2500000000 : ℝ), (-2305433583/10000000000 : ℝ), (5860602591/10000000000 : ℝ)] ![(275942350057/781250000000 : ℝ), (7401948353713/50000000000000 : ℝ), (6234435308139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124018249/2500000000 : ℝ)|^69 ≤ (275942350057/781250000000 : ℝ)^53
        have hw : |(1124018249/2500000000 : ℝ)|=(1124018249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2305433583/10000000000 : ℝ)|^69 ≤ (7401948353713/50000000000000 : ℝ)^53
        have hw : |(-2305433583/10000000000 : ℝ)|=(2305433583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5860602591/10000000000 : ℝ)|^69 ≤ (6234435308139/12500000000000 : ℝ)^53
        have hw : |(5860602591/10000000000 : ℝ)|=(5860602591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2251939723/5000000000 : ℝ)*x 0 + (5857029697/10000000000 : ℝ)*x 1 + (-57515347/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251939723/5000000000 : ℝ)^69 ≤ (35400481953187/100000000000000 : ℝ)^53 := by
    have hnat : (2251939723 : ℕ)^69*100000000000000^53 ≤ 35400481953187^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251939723 5000000000 35400481953187 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5857029697/10000000000 : ℝ)^69 ≤ (49835900421057/100000000000000 : ℝ)^53 := by
    have hnat : (5857029697 : ℕ)^69*100000000000000^53 ≤ 49835900421057^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857029697 10000000000 49835900421057 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57515347/250000000 : ℝ)^69 ≤ (738180880201/5000000000000 : ℝ)^53 := by
    have hnat : (57515347 : ℕ)^69*5000000000000^53 ≤ 738180880201^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57515347 250000000 738180880201 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251939723/5000000000 : ℝ), (5857029697/10000000000 : ℝ), (-57515347/250000000 : ℝ)] ![(35400481953187/100000000000000 : ℝ), (49835900421057/100000000000000 : ℝ), (738180880201/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251939723/5000000000 : ℝ)|^69 ≤ (35400481953187/100000000000000 : ℝ)^53
        have hw : |(2251939723/5000000000 : ℝ)|=(2251939723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5857029697/10000000000 : ℝ)|^69 ≤ (49835900421057/100000000000000 : ℝ)^53
        have hw : |(5857029697/10000000000 : ℝ)|=(5857029697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57515347/250000000 : ℝ)|^69 ≤ (738180880201/5000000000000 : ℝ)^53
        have hw : |(-57515347/250000000 : ℝ)|=(57515347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6198611037/10000000000 : ℝ)*x 0 + (203546499/625000000 : ℝ)*x 1 + (1624318193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6198611037/10000000000 : ℝ)^69 ≤ (53652603794321/100000000000000 : ℝ)^53 := by
    have hnat : (6198611037 : ℕ)^69*100000000000000^53 ≤ 53652603794321^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6198611037 10000000000 53652603794321 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203546499/625000000 : ℝ)^69 ≤ (4642259620481/20000000000000 : ℝ)^53 := by
    have hnat : (203546499 : ℕ)^69*20000000000000^53 ≤ 4642259620481^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203546499 625000000 4642259620481 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1624318193/5000000000 : ℝ)^69 ≤ (5784024522281/25000000000000 : ℝ)^53 := by
    have hnat : (1624318193 : ℕ)^69*25000000000000^53 ≤ 5784024522281^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624318193 5000000000 5784024522281 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6198611037/10000000000 : ℝ), (203546499/625000000 : ℝ), (1624318193/5000000000 : ℝ)] ![(53652603794321/100000000000000 : ℝ), (4642259620481/20000000000000 : ℝ), (5784024522281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6198611037/10000000000 : ℝ)|^69 ≤ (53652603794321/100000000000000 : ℝ)^53
        have hw : |(6198611037/10000000000 : ℝ)|=(6198611037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203546499/625000000 : ℝ)|^69 ≤ (4642259620481/20000000000000 : ℝ)^53
        have hw : |(203546499/625000000 : ℝ)|=(203546499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1624318193/5000000000 : ℝ)|^69 ≤ (5784024522281/25000000000000 : ℝ)^53
        have hw : |(1624318193/5000000000 : ℝ)|=(1624318193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2779274041/10000000000 : ℝ)*x 0 + (76980559/156250000 : ℝ)*x 1 + (2536382041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2779274041/10000000000 : ℝ)^69 ≤ (18882591430887/100000000000000 : ℝ)^53 := by
    have hnat : (2779274041 : ℕ)^69*100000000000000^53 ≤ 18882591430887^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779274041 10000000000 18882591430887 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76980559/156250000 : ℝ)^69 ≤ (39787739992193/100000000000000 : ℝ)^53 := by
    have hnat : (76980559 : ℕ)^69*100000000000000^53 ≤ 39787739992193^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76980559 156250000 39787739992193 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536382041/5000000000 : ℝ)^69 ≤ (4132966856367/10000000000000 : ℝ)^53 := by
    have hnat : (2536382041 : ℕ)^69*10000000000000^53 ≤ 4132966856367^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536382041 5000000000 4132966856367 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2779274041/10000000000 : ℝ), (76980559/156250000 : ℝ), (2536382041/5000000000 : ℝ)] ![(18882591430887/100000000000000 : ℝ), (39787739992193/100000000000000 : ℝ), (4132966856367/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2779274041/10000000000 : ℝ)|^69 ≤ (18882591430887/100000000000000 : ℝ)^53
        have hw : |(-2779274041/10000000000 : ℝ)|=(2779274041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76980559/156250000 : ℝ)|^69 ≤ (39787739992193/100000000000000 : ℝ)^53
        have hw : |(76980559/156250000 : ℝ)|=(76980559/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536382041/5000000000 : ℝ)|^69 ≤ (4132966856367/10000000000000 : ℝ)^53
        have hw : |(2536382041/5000000000 : ℝ)|=(2536382041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (224151043/500000000 : ℝ)*x 0 + (-2272072357/10000000000 : ℝ)*x 1 + (2948863663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224151043/500000000 : ℝ)^69 ≤ (8796797254317/25000000000000 : ℝ)^53 := by
    have hnat : (224151043 : ℕ)^69*25000000000000^53 ≤ 8796797254317^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224151043 500000000 8796797254317 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272072357/10000000000 : ℝ)^69 ≤ (453925446201/3125000000000 : ℝ)^53 := by
    have hnat : (2272072357 : ℕ)^69*3125000000000^53 ≤ 453925446201^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272072357 10000000000 453925446201 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2948863663/5000000000 : ℝ)^69 ≤ (50287196689361/100000000000000 : ℝ)^53 := by
    have hnat : (2948863663 : ℕ)^69*100000000000000^53 ≤ 50287196689361^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2948863663 5000000000 50287196689361 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224151043/500000000 : ℝ), (-2272072357/10000000000 : ℝ), (2948863663/5000000000 : ℝ)] ![(8796797254317/25000000000000 : ℝ), (453925446201/3125000000000 : ℝ), (50287196689361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224151043/500000000 : ℝ)|^69 ≤ (8796797254317/25000000000000 : ℝ)^53
        have hw : |(224151043/500000000 : ℝ)|=(224151043/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2272072357/10000000000 : ℝ)|^69 ≤ (453925446201/3125000000000 : ℝ)^53
        have hw : |(-2272072357/10000000000 : ℝ)|=(2272072357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2948863663/5000000000 : ℝ)|^69 ≤ (50287196689361/100000000000000 : ℝ)^53
        have hw : |(2948863663/5000000000 : ℝ)|=(2948863663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2245413127/5000000000 : ℝ)*x 0 + (740262079/1250000000 : ℝ)*x 1 + (-2229846221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245413127/5000000000 : ℝ)^69 ≤ (35266969367843/100000000000000 : ℝ)^53 := by
    have hnat : (2245413127 : ℕ)^69*100000000000000^53 ≤ 35266969367843^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245413127 5000000000 35266969367843 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740262079/1250000000 : ℝ)^69 ≤ (6319734856853/12500000000000 : ℝ)^53 := by
    have hnat : (740262079 : ℕ)^69*12500000000000^53 ≤ 6319734856853^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740262079 1250000000 6319734856853 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229846221/10000000000 : ℝ)^69 ≤ (2835030353943/20000000000000 : ℝ)^53 := by
    have hnat : (2229846221 : ℕ)^69*20000000000000^53 ≤ 2835030353943^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229846221 10000000000 2835030353943 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245413127/5000000000 : ℝ), (740262079/1250000000 : ℝ), (-2229846221/10000000000 : ℝ)] ![(35266969367843/100000000000000 : ℝ), (6319734856853/12500000000000 : ℝ), (2835030353943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245413127/5000000000 : ℝ)|^69 ≤ (35266969367843/100000000000000 : ℝ)^53
        have hw : |(2245413127/5000000000 : ℝ)|=(2245413127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740262079/1250000000 : ℝ)|^69 ≤ (6319734856853/12500000000000 : ℝ)^53
        have hw : |(740262079/1250000000 : ℝ)|=(740262079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229846221/10000000000 : ℝ)|^69 ≤ (2835030353943/20000000000000 : ℝ)^53
        have hw : |(-2229846221/10000000000 : ℝ)|=(2229846221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1239011019/2000000000 : ℝ)*x 0 + (1669629787/5000000000 : ℝ)*x 1 + (1584887751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239011019/2000000000 : ℝ)^69 ≤ (53612536806389/100000000000000 : ℝ)^53 := by
    have hnat : (1239011019 : ℕ)^69*100000000000000^53 ≤ 53612536806389^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239011019 2000000000 53612536806389 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669629787/5000000000 : ℝ)^69 ≤ (11989924954771/50000000000000 : ℝ)^53 := by
    have hnat : (1669629787 : ℕ)^69*50000000000000^53 ≤ 11989924954771^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669629787 5000000000 11989924954771 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584887751/5000000000 : ℝ)^69 ≤ (22407613262737/100000000000000 : ℝ)^53 := by
    have hnat : (1584887751 : ℕ)^69*100000000000000^53 ≤ 22407613262737^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584887751 5000000000 22407613262737 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1239011019/2000000000 : ℝ), (1669629787/5000000000 : ℝ), (1584887751/5000000000 : ℝ)] ![(53612536806389/100000000000000 : ℝ), (11989924954771/50000000000000 : ℝ), (22407613262737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1239011019/2000000000 : ℝ)|^69 ≤ (53612536806389/100000000000000 : ℝ)^53
        have hw : |(1239011019/2000000000 : ℝ)|=(1239011019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1669629787/5000000000 : ℝ)|^69 ≤ (11989924954771/50000000000000 : ℝ)^53
        have hw : |(1669629787/5000000000 : ℝ)|=(1669629787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584887751/5000000000 : ℝ)|^69 ≤ (22407613262737/100000000000000 : ℝ)^53
        have hw : |(1584887751/5000000000 : ℝ)|=(1584887751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2712326621/10000000000 : ℝ)*x 0 + (2495095473/5000000000 : ℝ)*x 1 + (5065385469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712326621/10000000000 : ℝ)^69 ≤ (3658519819131/20000000000000 : ℝ)^53 := by
    have hnat : (2712326621 : ℕ)^69*20000000000000^53 ≤ 3658519819131^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712326621 10000000000 3658519819131 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495095473/5000000000 : ℝ)^69 ≤ (1618239188413/4000000000000 : ℝ)^53 := by
    have hnat : (2495095473 : ℕ)^69*4000000000000^53 ≤ 1618239188413^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495095473 5000000000 1618239188413 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5065385469/10000000000 : ℝ)^69 ≤ (41251421181509/100000000000000 : ℝ)^53 := by
    have hnat : (5065385469 : ℕ)^69*100000000000000^53 ≤ 41251421181509^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065385469 10000000000 41251421181509 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2712326621/10000000000 : ℝ), (2495095473/5000000000 : ℝ), (5065385469/10000000000 : ℝ)] ![(3658519819131/20000000000000 : ℝ), (1618239188413/4000000000000 : ℝ), (41251421181509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2712326621/10000000000 : ℝ)|^69 ≤ (3658519819131/20000000000000 : ℝ)^53
        have hw : |(-2712326621/10000000000 : ℝ)|=(2712326621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495095473/5000000000 : ℝ)|^69 ≤ (1618239188413/4000000000000 : ℝ)^53
        have hw : |(2495095473/5000000000 : ℝ)|=(2495095473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5065385469/10000000000 : ℝ)|^69 ≤ (41251421181509/100000000000000 : ℝ)^53
        have hw : |(5065385469/10000000000 : ℝ)|=(5065385469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2229735911/5000000000 : ℝ)*x 0 + (-2293545577/10000000000 : ℝ)*x 1 + (5903263763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2229735911/5000000000 : ℝ)^69 ≤ (34946744268599/100000000000000 : ℝ)^53 := by
    have hnat : (2229735911 : ℕ)^69*100000000000000^53 ≤ 34946744268599^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229735911 5000000000 34946744268599 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2293545577/10000000000 : ℝ)^69 ≤ (14704592625739/100000000000000 : ℝ)^53 := by
    have hnat : (2293545577 : ℕ)^69*100000000000000^53 ≤ 14704592625739^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293545577 10000000000 14704592625739 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5903263763/10000000000 : ℝ)^69 ≤ (251743315491/500000000000 : ℝ)^53 := by
    have hnat : (5903263763 : ℕ)^69*500000000000^53 ≤ 251743315491^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5903263763 10000000000 251743315491 500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2229735911/5000000000 : ℝ), (-2293545577/10000000000 : ℝ), (5903263763/10000000000 : ℝ)] ![(34946744268599/100000000000000 : ℝ), (14704592625739/100000000000000 : ℝ), (251743315491/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2229735911/5000000000 : ℝ)|^69 ≤ (34946744268599/100000000000000 : ℝ)^53
        have hw : |(2229735911/5000000000 : ℝ)|=(2229735911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2293545577/10000000000 : ℝ)|^69 ≤ (14704592625739/100000000000000 : ℝ)^53
        have hw : |(-2293545577/10000000000 : ℝ)|=(2293545577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5903263763/10000000000 : ℝ)|^69 ≤ (251743315491/500000000000 : ℝ)^53
        have hw : |(5903263763/10000000000 : ℝ)|=(5903263763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4572626613/10000000000 : ℝ)*x 0 + (1460244889/2500000000 : ℝ)*x 1 + (-2237224419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4572626613/10000000000 : ℝ)^69 ≤ (7221114984461/20000000000000 : ℝ)^53 := by
    have hnat : (4572626613 : ℕ)^69*20000000000000^53 ≤ 7221114984461^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572626613 10000000000 7221114984461 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1460244889/2500000000 : ℝ)^69 ≤ (2482909003429/5000000000000 : ℝ)^53 := by
    have hnat : (1460244889 : ℕ)^69*5000000000000^53 ≤ 2482909003429^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460244889 2500000000 2482909003429 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237224419/10000000000 : ℝ)^69 ≤ (7118122494953/50000000000000 : ℝ)^53 := by
    have hnat : (2237224419 : ℕ)^69*50000000000000^53 ≤ 7118122494953^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237224419 10000000000 7118122494953 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4572626613/10000000000 : ℝ), (1460244889/2500000000 : ℝ), (-2237224419/10000000000 : ℝ)] ![(7221114984461/20000000000000 : ℝ), (2482909003429/5000000000000 : ℝ), (7118122494953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4572626613/10000000000 : ℝ)|^69 ≤ (7221114984461/20000000000000 : ℝ)^53
        have hw : |(4572626613/10000000000 : ℝ)|=(4572626613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1460244889/2500000000 : ℝ)|^69 ≤ (2482909003429/5000000000000 : ℝ)^53
        have hw : |(1460244889/2500000000 : ℝ)|=(1460244889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237224419/10000000000 : ℝ)|^69 ≤ (7118122494953/50000000000000 : ℝ)^53
        have hw : |(-2237224419/10000000000 : ℝ)|=(2237224419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1255402587/2000000000 : ℝ)*x 0 + (3251570651/10000000000 : ℝ)*x 1 + (1578979681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1255402587/2000000000 : ℝ)^69 ≤ (27268882271811/50000000000000 : ℝ)^53 := by
    have hnat : (1255402587 : ℕ)^69*50000000000000^53 ≤ 27268882271811^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255402587 2000000000 27268882271811 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3251570651/10000000000 : ℝ)^69 ≤ (23163307601629/100000000000000 : ℝ)^53 := by
    have hnat : (3251570651 : ℕ)^69*100000000000000^53 ≤ 23163307601629^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3251570651 10000000000 23163307601629 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578979681/5000000000 : ℝ)^69 ≤ (4459785568201/20000000000000 : ℝ)^53 := by
    have hnat : (1578979681 : ℕ)^69*20000000000000^53 ≤ 4459785568201^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578979681 5000000000 4459785568201 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1255402587/2000000000 : ℝ), (3251570651/10000000000 : ℝ), (1578979681/5000000000 : ℝ)] ![(27268882271811/50000000000000 : ℝ), (23163307601629/100000000000000 : ℝ), (4459785568201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1255402587/2000000000 : ℝ)|^69 ≤ (27268882271811/50000000000000 : ℝ)^53
        have hw : |(1255402587/2000000000 : ℝ)|=(1255402587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3251570651/10000000000 : ℝ)|^69 ≤ (23163307601629/100000000000000 : ℝ)^53
        have hw : |(3251570651/10000000000 : ℝ)|=(3251570651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1578979681/5000000000 : ℝ)|^69 ≤ (4459785568201/20000000000000 : ℝ)^53
        have hw : |(1578979681/5000000000 : ℝ)|=(1578979681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-338267003/1250000000 : ℝ)*x 0 + (2514452329/5000000000 : ℝ)*x 1 + (251594629/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338267003/1250000000 : ℝ)^69 ≤ (18238262871127/100000000000000 : ℝ)^53 := by
    have hnat : (338267003 : ℕ)^69*100000000000000^53 ≤ 18238262871127^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338267003 1250000000 18238262871127 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2514452329/5000000000 : ℝ)^69 ≤ (40865062254203/100000000000000 : ℝ)^53 := by
    have hnat : (2514452329 : ℕ)^69*100000000000000^53 ≤ 40865062254203^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514452329 5000000000 40865062254203 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251594629/500000000 : ℝ)^69 ≤ (40896674851693/100000000000000 : ℝ)^53 := by
    have hnat : (251594629 : ℕ)^69*100000000000000^53 ≤ 40896674851693^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251594629 500000000 40896674851693 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338267003/1250000000 : ℝ), (2514452329/5000000000 : ℝ), (251594629/500000000 : ℝ)] ![(18238262871127/100000000000000 : ℝ), (40865062254203/100000000000000 : ℝ), (40896674851693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338267003/1250000000 : ℝ)|^69 ≤ (18238262871127/100000000000000 : ℝ)^53
        have hw : |(-338267003/1250000000 : ℝ)|=(338267003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2514452329/5000000000 : ℝ)|^69 ≤ (40865062254203/100000000000000 : ℝ)^53
        have hw : |(2514452329/5000000000 : ℝ)|=(2514452329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251594629/500000000 : ℝ)|^69 ≤ (40896674851693/100000000000000 : ℝ)^53
        have hw : |(251594629/500000000 : ℝ)|=(251594629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2285505769/5000000000 : ℝ)*x 0 + (-2246337463/10000000000 : ℝ)*x 1 + (583565363/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285505769/5000000000 : ℝ)^69 ≤ (36088973271129/100000000000000 : ℝ)^53 := by
    have hnat : (2285505769 : ℕ)^69*100000000000000^53 ≤ 36088973271129^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285505769 5000000000 36088973271129 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246337463/10000000000 : ℝ)^69 ≤ (14311787129479/100000000000000 : ℝ)^53 := by
    have hnat : (2246337463 : ℕ)^69*100000000000000^53 ≤ 14311787129479^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246337463 10000000000 14311787129479 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583565363/1000000000 : ℝ)^69 ≤ (49599239588127/100000000000000 : ℝ)^53 := by
    have hnat : (583565363 : ℕ)^69*100000000000000^53 ≤ 49599239588127^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583565363 1000000000 49599239588127 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2285505769/5000000000 : ℝ), (-2246337463/10000000000 : ℝ), (583565363/1000000000 : ℝ)] ![(36088973271129/100000000000000 : ℝ), (14311787129479/100000000000000 : ℝ), (49599239588127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2285505769/5000000000 : ℝ)|^69 ≤ (36088973271129/100000000000000 : ℝ)^53
        have hw : |(2285505769/5000000000 : ℝ)|=(2285505769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246337463/10000000000 : ℝ)|^69 ≤ (14311787129479/100000000000000 : ℝ)^53
        have hw : |(-2246337463/10000000000 : ℝ)|=(2246337463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(583565363/1000000000 : ℝ)|^69 ≤ (49599239588127/100000000000000 : ℝ)^53
        have hw : |(583565363/1000000000 : ℝ)|=(583565363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (892801853/2000000000 : ℝ)*x 0 + (2955494681/5000000000 : ℝ)*x 1 + (-1138851329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892801853/2000000000 : ℝ)^69 ≤ (34993043563863/100000000000000 : ℝ)^53 := by
    have hnat : (892801853 : ℕ)^69*100000000000000^53 ≤ 34993043563863^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892801853 2000000000 34993043563863 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2955494681/5000000000 : ℝ)^69 ≤ (50434463020399/100000000000000 : ℝ)^53 := by
    have hnat : (2955494681 : ℕ)^69*100000000000000^53 ≤ 50434463020399^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955494681 5000000000 50434463020399 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138851329/5000000000 : ℝ)^69 ≤ (2914498680871/20000000000000 : ℝ)^53 := by
    have hnat : (1138851329 : ℕ)^69*20000000000000^53 ≤ 2914498680871^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138851329 5000000000 2914498680871 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(892801853/2000000000 : ℝ), (2955494681/5000000000 : ℝ), (-1138851329/5000000000 : ℝ)] ![(34993043563863/100000000000000 : ℝ), (50434463020399/100000000000000 : ℝ), (2914498680871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(892801853/2000000000 : ℝ)|^69 ≤ (34993043563863/100000000000000 : ℝ)^53
        have hw : |(892801853/2000000000 : ℝ)|=(892801853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2955494681/5000000000 : ℝ)|^69 ≤ (50434463020399/100000000000000 : ℝ)^53
        have hw : |(2955494681/5000000000 : ℝ)|=(2955494681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1138851329/5000000000 : ℝ)|^69 ≤ (2914498680871/20000000000000 : ℝ)^53
        have hw : |(-1138851329/5000000000 : ℝ)|=(1138851329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s5_s5_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3141994079/5000000000 : ℝ)*x 0 + (3199881653/10000000000 : ℝ)*x 1 + (3201306929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3141994079/5000000000 : ℝ)^69 ≤ (6827084690533/12500000000000 : ℝ)^53 := by
    have hnat : (3141994079 : ℕ)^69*12500000000000^53 ≤ 6827084690533^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3141994079 5000000000 6827084690533 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3199881653/10000000000 : ℝ)^69 ≤ (11342541735737/50000000000000 : ℝ)^53 := by
    have hnat : (3199881653 : ℕ)^69*50000000000000^53 ≤ 11342541735737^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3199881653 10000000000 11342541735737 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3201306929/10000000000 : ℝ)^69 ≤ (22698238986449/100000000000000 : ℝ)^53 := by
    have hnat : (3201306929 : ℕ)^69*100000000000000^53 ≤ 22698238986449^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3201306929 10000000000 22698238986449 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3141994079/5000000000 : ℝ), (3199881653/10000000000 : ℝ), (3201306929/10000000000 : ℝ)] ![(6827084690533/12500000000000 : ℝ), (11342541735737/50000000000000 : ℝ), (22698238986449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3141994079/5000000000 : ℝ)|^69 ≤ (6827084690533/12500000000000 : ℝ)^53
        have hw : |(3141994079/5000000000 : ℝ)|=(3141994079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3199881653/10000000000 : ℝ)|^69 ≤ (11342541735737/50000000000000 : ℝ)^53
        have hw : |(3199881653/10000000000 : ℝ)|=(3199881653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3201306929/10000000000 : ℝ)|^69 ≤ (22698238986449/100000000000000 : ℝ)^53
        have hw : |(3201306929/10000000000 : ℝ)|=(3201306929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308053_s5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((3939/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3939/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4577/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4577/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4401/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4401/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1793/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1793/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8851/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8851/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8779/50000 : ℝ)*X 1 2) := by
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
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (3939/12500 : ℝ) ^ (17/4 : ℝ) ≤ (738793155261983333/100000000000000000000 : ℝ) := by
    have hpowers : (3939/12500 : ℝ)^17 ≤ (738793155261983333/100000000000000000000 : ℝ)^4 := by
      have hnat : (3939 : ℕ)^17*100000000000000000000^4 ≤ 738793155261983333^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3939 12500 738793155261983333 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3939/12500 : ℝ)) (X := (738793155261983333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner0a : (100738793155261983333/100000000000000000000 : ℝ) ≤ (2003466895236557/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100738793155261983333/100000000000000000000 : ℝ)^4 ≤ (2003466895236557/2000000000000000 : ℝ)^17 := by
      have hnat : (100738793155261983333 : ℕ)^4*2000000000000000^17 ≤ 2003466895236557^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100738793155261983333 100000000000000000000 2003466895236557 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003466895236557/2000000000000000 : ℝ)) (X := (100738793155261983333/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner0b : (50738793155261983333/50000000000000000000 : ℝ) ≤ (5017286004352817/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50738793155261983333/50000000000000000000 : ℝ)^4 ≤ (5017286004352817/5000000000000000 : ℝ)^17 := by
      have hnat : (50738793155261983333 : ℕ)^4*5000000000000000^17 ≤ 5017286004352817^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50738793155261983333 50000000000000000000 5017286004352817 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017286004352817/5000000000000000 : ℝ)) (X := (50738793155261983333/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1155631745519/210080000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5745844174283/1050400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3939/12500 : ℝ)) (alpha := (1155631745519/210080000000000 : ℝ)) (beta := (5745844174283/1050400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3939/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1155631745519/210080000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5745844174283/1050400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (4577/12500 : ℝ) ^ (17/4 : ℝ) ≤ (139830310663065967/10000000000000000000 : ℝ) := by
    have hpowers : (4577/12500 : ℝ)^17 ≤ (139830310663065967/10000000000000000000 : ℝ)^4 := by
      have hnat : (4577 : ℕ)^17*10000000000000000000^4 ≤ 139830310663065967^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4577 12500 139830310663065967 10000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4577/12500 : ℝ)) (X := (139830310663065967/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner1a : (10139830310663065967/10000000000000000000 : ℝ) ≤ (10032726777616937/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10139830310663065967/10000000000000000000 : ℝ)^4 ≤ (10032726777616937/10000000000000000 : ℝ)^17 := by
      have hnat : (10139830310663065967 : ℕ)^4*10000000000000000^17 ≤ 10032726777616937^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10139830310663065967 10000000000000000000 10032726777616937 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032726777616937/10000000000000000 : ℝ)) (X := (10139830310663065967/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner1b : (5139830310663065967/5000000000000000000 : ℝ) ≤ (31453469484527/31250000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5139830310663065967/5000000000000000000 : ℝ)^4 ≤ (31453469484527/31250000000000 : ℝ)^17 := by
      have hnat : (5139830310663065967 : ℕ)^4*31250000000000^17 ≤ 31453469484527^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5139830310663065967 5000000000000000000 31453469484527 31250000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31453469484527/31250000000000 : ℝ)) (X := (5139830310663065967/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(32726777616937/3661600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(32383457431703/3661600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (4577/12500 : ℝ)) (alpha := (32726777616937/3661600000000000 : ℝ)) (beta := (32383457431703/3661600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (4577/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(32726777616937/3661600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(32383457431703/3661600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (4401/12500 : ℝ) ^ (17/4 : ℝ) ≤ (1183656701014399307/100000000000000000000 : ℝ) := by
    have hpowers : (4401/12500 : ℝ)^17 ≤ (1183656701014399307/100000000000000000000 : ℝ)^4 := by
      have hnat : (4401 : ℕ)^17*100000000000000000000^4 ≤ 1183656701014399307^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4401 12500 1183656701014399307 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4401/12500 : ℝ)) (X := (1183656701014399307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner2a : (101183656701014399307/100000000000000000000 : ℝ) ≤ (2506931392749161/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (101183656701014399307/100000000000000000000 : ℝ)^4 ≤ (2506931392749161/2500000000000000 : ℝ)^17 := by
      have hnat : (101183656701014399307 : ℕ)^4*2500000000000000^17 ≤ 2506931392749161^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101183656701014399307 100000000000000000000 2506931392749161 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506931392749161/2500000000000000 : ℝ)) (X := (101183656701014399307/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s5_corner2b : (51183656701014399307/50000000000000000000 : ℝ) ≤ (2011040843646047/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (51183656701014399307/50000000000000000000 : ℝ)^4 ≤ (2011040843646047/2000000000000000 : ℝ)^17 := by
      have hnat : (51183656701014399307 : ℕ)^4*2000000000000000^17 ≤ 2011040843646047^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51183656701014399307 50000000000000000000 2011040843646047 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011040843646047/2000000000000000 : ℝ)) (X := (51183656701014399307/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6931392749161/880200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(27478647233591/3520800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (4401/12500 : ℝ)) (alpha := (6931392749161/880200000000000 : ℝ)) (beta := (27478647233591/3520800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (4401/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6931392749161/880200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(27478647233591/3520800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2780858823/10000000000 : ℝ)*X 0 0+(1249183293/2500000000 : ℝ)*X 0 1+(5001780639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((1124018249/2500000000 : ℝ)*X 1 0+(-2305433583/10000000000 : ℝ)*X 1 1+(5860602591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((2251939723/5000000000 : ℝ)*X 2 0+(5857029697/10000000000 : ℝ)*X 2 1+(-57515347/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((6198611037/10000000000 : ℝ)*X 0 0+(203546499/625000000 : ℝ)*X 0 1+(1624318193/5000000000 : ℝ)*X 0 2+(6198611037/10000000000 : ℝ)*X 1 0+(203546499/625000000 : ℝ)*X 1 1+(1624318193/5000000000 : ℝ)*X 1 2+(6198611037/10000000000 : ℝ)*X 2 0+(203546499/625000000 : ℝ)*X 2 1+(1624318193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-2779274041/10000000000 : ℝ)*X 0 0+(76980559/156250000 : ℝ)*X 0 1+(2536382041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((224151043/500000000 : ℝ)*X 1 0+(-2272072357/10000000000 : ℝ)*X 1 1+(2948863663/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((2245413127/5000000000 : ℝ)*X 2 0+(740262079/1250000000 : ℝ)*X 2 1+(-2229846221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((1239011019/2000000000 : ℝ)*X 0 0+(1669629787/5000000000 : ℝ)*X 0 1+(1584887751/5000000000 : ℝ)*X 0 2+(1239011019/2000000000 : ℝ)*X 1 0+(1669629787/5000000000 : ℝ)*X 1 1+(1584887751/5000000000 : ℝ)*X 1 2+(1239011019/2000000000 : ℝ)*X 2 0+(1669629787/5000000000 : ℝ)*X 2 1+(1584887751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-2712326621/10000000000 : ℝ)*X 0 0+(2495095473/5000000000 : ℝ)*X 0 1+(5065385469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((2229735911/5000000000 : ℝ)*X 1 0+(-2293545577/10000000000 : ℝ)*X 1 1+(5903263763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((4572626613/10000000000 : ℝ)*X 2 0+(1460244889/2500000000 : ℝ)*X 2 1+(-2237224419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((1255402587/2000000000 : ℝ)*X 0 0+(3251570651/10000000000 : ℝ)*X 0 1+(1578979681/5000000000 : ℝ)*X 0 2+(1255402587/2000000000 : ℝ)*X 1 0+(3251570651/10000000000 : ℝ)*X 1 1+(1578979681/5000000000 : ℝ)*X 1 2+(1255402587/2000000000 : ℝ)*X 2 0+(3251570651/10000000000 : ℝ)*X 2 1+(1578979681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-338267003/1250000000 : ℝ)*X 0 0+(2514452329/5000000000 : ℝ)*X 0 1+(251594629/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((2285505769/5000000000 : ℝ)*X 1 0+(-2246337463/10000000000 : ℝ)*X 1 1+(583565363/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((892801853/2000000000 : ℝ)*X 2 0+(2955494681/5000000000 : ℝ)*X 2 1+(-1138851329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((3141994079/5000000000 : ℝ)*X 0 0+(3199881653/10000000000 : ℝ)*X 0 1+(3201306929/10000000000 : ℝ)*X 0 2+(3141994079/5000000000 : ℝ)*X 1 0+(3199881653/10000000000 : ℝ)*X 1 1+(3201306929/10000000000 : ℝ)*X 1 2+(3141994079/5000000000 : ℝ)*X 2 0+(3199881653/10000000000 : ℝ)*X 2 1+(3201306929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((1793/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1793/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31299000787214016721339784321/1763216933400000000000000000000000 : ℝ) := by norm_num
    linear_combination (868931804453/125000000000 : ℝ)*(base49) + (7668240267667/1000000000000 : ℝ)*(base59) + (57657/15625000000 : ℝ)*(base60) + (35453492247241/500000000000 : ℝ)*(major_s5_0) + (35453492247241/500000000000 : ℝ)*(major_s5_1) + (35453492247241/500000000000 : ℝ)*(major_s5_2) + (671362843/500000000000 : ℝ)*(sp_s5_0) + (329116993/1000000000000 : ℝ)*(sp_s5_6) + (48282823470059/500000000000 : ℝ)*(sp_s5_7) + (96564301422323/1000000000000 : ℝ)*(sp_s5_8) + (6035268229963/62500000000 : ℝ)*(sp_s5_9) + (22623322144569/500000000000 : ℝ)*(sp_s5_13) + (2688243481/1000000000000 : ℝ)*(sp_s5_15) + (674496599/250000000000 : ℝ)*(sp_s5_23) + (45246973406131/1000000000000 : ℝ)*(f.failure) + (24141747416451/250000000000 : ℝ)*(f.sum) + (122172179775922699/322294032000000000000000000000 : ℝ)*base62 + (718977348051791/1760400000000000000000000000 : ℝ)*base64 + (983490337618257/1830800000000000000000000000 : ℝ)*base67 + (113955007857329/440100000000000000000000000 : ℝ)*base68 + (307961182205724007/577851300000000000000000000000 : ℝ)*base70 + (57546089828203/525200000000000000000000000 : ℝ)*base73 + (187637125997977/1830800000000000000000000000 : ℝ)*base75 + (11858114674951/105040000000000000000000000 : ℝ)*base77 + (249674221504396553/600960100000000000000000000000 : ℝ)*base79 + (4859/100000000000000000 : ℝ)*base86 + (4859/100000000000000000 : ℝ)*base88 + (4859/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8851/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8851/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25166705700562587/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (6955747845723/1000000000000 : ℝ)*(base49) + (3574311896821/500000000000 : ℝ)*(base59) + (69700515077729/1000000000000 : ℝ)*(major_s5_0) + (69700515077729/1000000000000 : ℝ)*(major_s5_1) + (69700515077729/1000000000000 : ℝ)*(major_s5_2) + (2797345731/1000000000000 : ℝ)*(sp_s5_1) + (175419771/250000000000 : ℝ)*(sp_s5_2) + (52342741/40000000000 : ℝ)*(sp_s5_6) + (1378817099/1000000000000 : ℝ)*(sp_s5_7) + (94922543581869/1000000000000 : ℝ)*(sp_s5_14) + (94921125053237/1000000000000 : ℝ)*(sp_s5_15) + (18984644143977/200000000000 : ℝ)*(sp_s5_16) + (1779000747767/40000000000 : ℝ)*(sp_s5_20) + (388569111/500000000000 : ℝ)*(sp_s5_27) + (22238552200461/500000000000 : ℝ)*(f.failure) + (94923922398969/1000000000000 : ℝ)*(f.sum) + (938197078329338791/3222940320000000000000000000000 : ℝ)*base62 + (720011440326041/3520800000000000000000000000 : ℝ)*base65 + (1702240489428793/3661600000000000000000000000 : ℝ)*base67 + (541086826987049/880200000000000000000000000 : ℝ)*base69 + (819112743611995403/1155702600000000000000000000000 : ℝ)*base70 + (794965157509707/1050400000000000000000000000 : ℝ)*base73 + (609257327750873/3661600000000000000000000000 : ℝ)*base75 + (38352919918559/210080000000000000000000000 : ℝ)*base77 + (273158467915658383/1201920200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (6229/50000000000000000 : ℝ)*base86 + (6229/50000000000000000 : ℝ)*base88 + (6229/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8779/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7353941951408880196687/586800000000000000000000000 : ℝ) := by norm_num
    linear_combination (5910516759/25000000000 : ℝ)*(base40) + (6321889385123/1000000000000 : ℝ)*(base49) + (1648942117291/250000000000 : ℝ)*(base59) + (63957502162097/1000000000000 : ℝ)*(major_s5_0) + (63957502162097/1000000000000 : ℝ)*(major_s5_1) + (63957502162097/1000000000000 : ℝ)*(major_s5_2) + (318105249/500000000000 : ℝ)*(sp_s5_0) + (1824583699/1000000000000 : ℝ)*(sp_s5_2) + (119080581/200000000000 : ℝ)*(sp_s5_6) + (446168327/200000000000 : ℝ)*(sp_s5_20) + (8710197542359/100000000000 : ℝ)*(sp_s5_21) + (10887826454261/125000000000 : ℝ)*(sp_s5_22) + (87100787050389/1000000000000 : ℝ)*(sp_s5_23) + (20404781134067/500000000000 : ℝ)*(sp_s5_27) + (20406194256337/500000000000 : ℝ)*(f.failure) + (10887826454261/125000000000 : ℝ)*(f.sum) + (1352405143653629129/3222940320000000000000000000000 : ℝ)*base63 + (289875499361033/3520800000000000000000000000 : ℝ)*base65 + (2209870786146471/3661600000000000000000000000 : ℝ)*base66 + (186461686651903/880200000000000000000000000 : ℝ)*base68 + (745221059087048461/1155702600000000000000000000000 : ℝ)*base71 + (354176509603589/1050400000000000000000000000 : ℝ)*base72 + (742654855964471/3661600000000000000000000000 : ℝ)*base74 + (98897681150081/210080000000000000000000000 : ℝ)*base76 + (113218426323766781/1201920200000000000000000000000 : ℝ)*base79 + (22393/50000000000000000 : ℝ)*base86 + (22393/50000000000000000 : ℝ)*base88 + (22393/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((3939/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3939/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4577/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4577/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4401/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4401/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1793/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1793/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8851/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8851/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8779/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308053_s5 p hpa hpb X hX hprev4

#print axioms solution
