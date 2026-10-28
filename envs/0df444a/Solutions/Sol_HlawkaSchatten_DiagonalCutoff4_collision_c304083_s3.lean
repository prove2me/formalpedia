-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304083_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:50:06.408505+00:00
-- url     : https://prove2.me/submissions/0805bdd3-17a7-4807-aec5-bb98be23d8b8

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
theorem collision_support_c304083_s3_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1403195383/5000000000 : ℝ)*x 0 + (196264833/400000000 : ℝ)*x 1 + (5182279653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1403195383/5000000000 : ℝ)^133 ≤ (58634606049/312500000000 : ℝ)^101 := by
    have hnat : (1403195383 : ℕ)^133*312500000000^101 ≤ 58634606049^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403195383 5000000000 58634606049 312500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196264833/400000000 : ℝ)^133 ≤ (19578643583321/50000000000000 : ℝ)^101 := by
    have hnat : (196264833 : ℕ)^133*50000000000000^101 ≤ 19578643583321^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196264833 400000000 19578643583321 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182279653/10000000000 : ℝ)^133 ≤ (42079638882093/100000000000000 : ℝ)^101 := by
    have hnat : (5182279653 : ℕ)^133*100000000000000^101 ≤ 42079638882093^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182279653 10000000000 42079638882093 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1403195383/5000000000 : ℝ), (196264833/400000000 : ℝ), (5182279653/10000000000 : ℝ)] ![(58634606049/312500000000 : ℝ), (19578643583321/50000000000000 : ℝ), (42079638882093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1403195383/5000000000 : ℝ)|^133 ≤ (58634606049/312500000000 : ℝ)^101
        have hw : |(-1403195383/5000000000 : ℝ)|=(1403195383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196264833/400000000 : ℝ)|^133 ≤ (19578643583321/50000000000000 : ℝ)^101
        have hw : |(196264833/400000000 : ℝ)|=(196264833/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182279653/10000000000 : ℝ)|^133 ≤ (42079638882093/100000000000000 : ℝ)^101
        have hw : |(5182279653/10000000000 : ℝ)|=(5182279653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (808747001/1250000000 : ℝ)*x 0 + (-16149569/100000000 : ℝ)*x 1 + (4464055623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808747001/1250000000 : ℝ)^133 ≤ (5636255147401/10000000000000 : ℝ)^101 := by
    have hnat : (808747001 : ℕ)^133*10000000000000^101 ≤ 5636255147401^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808747001 1250000000 5636255147401 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16149569/100000000 : ℝ)^133 ≤ (4531596548757/50000000000000 : ℝ)^101 := by
    have hnat : (16149569 : ℕ)^133*50000000000000^101 ≤ 4531596548757^101*100000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16149569 100000000 4531596548757 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4464055623/10000000000 : ℝ)^133 ≤ (6914851085067/20000000000000 : ℝ)^101 := by
    have hnat : (4464055623 : ℕ)^133*20000000000000^101 ≤ 6914851085067^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464055623 10000000000 6914851085067 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808747001/1250000000 : ℝ), (-16149569/100000000 : ℝ), (4464055623/10000000000 : ℝ)] ![(5636255147401/10000000000000 : ℝ), (4531596548757/50000000000000 : ℝ), (6914851085067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808747001/1250000000 : ℝ)|^133 ≤ (5636255147401/10000000000000 : ℝ)^101
        have hw : |(808747001/1250000000 : ℝ)|=(808747001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16149569/100000000 : ℝ)|^133 ≤ (4531596548757/50000000000000 : ℝ)^101
        have hw : |(-16149569/100000000 : ℝ)|=(16149569/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4464055623/10000000000 : ℝ)|^133 ≤ (6914851085067/20000000000000 : ℝ)^101
        have hw : |(4464055623/10000000000 : ℝ)|=(4464055623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (394382617/1000000000 : ℝ)*x 0 + (3028508679/5000000000 : ℝ)*x 1 + (-1414189169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394382617/1000000000 : ℝ)^133 ≤ (5873834494723/20000000000000 : ℝ)^101 := by
    have hnat : (394382617 : ℕ)^133*20000000000000^101 ≤ 5873834494723^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394382617 1000000000 5873834494723 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3028508679/5000000000 : ℝ)^133 ≤ (51673932449337/100000000000000 : ℝ)^101 := by
    have hnat : (3028508679 : ℕ)^133*100000000000000^101 ≤ 51673932449337^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3028508679 5000000000 51673932449337 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414189169/5000000000 : ℝ)^133 ≤ (1895689506793/10000000000000 : ℝ)^101 := by
    have hnat : (1414189169 : ℕ)^133*10000000000000^101 ≤ 1895689506793^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414189169 5000000000 1895689506793 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(394382617/1000000000 : ℝ), (3028508679/5000000000 : ℝ), (-1414189169/5000000000 : ℝ)] ![(5873834494723/20000000000000 : ℝ), (51673932449337/100000000000000 : ℝ), (1895689506793/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(394382617/1000000000 : ℝ)|^133 ≤ (5873834494723/20000000000000 : ℝ)^101
        have hw : |(394382617/1000000000 : ℝ)|=(394382617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3028508679/5000000000 : ℝ)|^133 ≤ (51673932449337/100000000000000 : ℝ)^101
        have hw : |(3028508679/5000000000 : ℝ)|=(3028508679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1414189169/5000000000 : ℝ)|^133 ≤ (1895689506793/10000000000000 : ℝ)^101
        have hw : |(-1414189169/5000000000 : ℝ)|=(1414189169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-290686087/1000000000 : ℝ)*x 0 + (4870454883/10000000000 : ℝ)*x 1 + (16045381/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290686087/1000000000 : ℝ)^133 ≤ (614143794727/3125000000000 : ℝ)^101 := by
    have hnat : (290686087 : ℕ)^133*3125000000000^101 ≤ 614143794727^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290686087 1000000000 614143794727 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870454883/10000000000 : ℝ)^133 ≤ (7755532943251/20000000000000 : ℝ)^101 := by
    have hnat : (4870454883 : ℕ)^133*20000000000000^101 ≤ 7755532943251^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870454883 10000000000 7755532943251 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16045381/31250000 : ℝ)^133 ≤ (8313946768523/20000000000000 : ℝ)^101 := by
    have hnat : (16045381 : ℕ)^133*20000000000000^101 ≤ 8313946768523^101*31250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16045381 31250000 8313946768523 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290686087/1000000000 : ℝ), (4870454883/10000000000 : ℝ), (16045381/31250000 : ℝ)] ![(614143794727/3125000000000 : ℝ), (7755532943251/20000000000000 : ℝ), (8313946768523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290686087/1000000000 : ℝ)|^133 ≤ (614143794727/3125000000000 : ℝ)^101
        have hw : |(-290686087/1000000000 : ℝ)|=(290686087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4870454883/10000000000 : ℝ)|^133 ≤ (7755532943251/20000000000000 : ℝ)^101
        have hw : |(4870454883/10000000000 : ℝ)|=(4870454883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16045381/31250000 : ℝ)|^133 ≤ (8313946768523/20000000000000 : ℝ)^101
        have hw : |(16045381/31250000 : ℝ)|=(16045381/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6350364093/10000000000 : ℝ)*x 0 + (-453751593/5000000000 : ℝ)*x 1 + (5058640829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6350364093/10000000000 : ℝ)^133 ≤ (27497232574841/50000000000000 : ℝ)^101 := by
    have hnat : (6350364093 : ℕ)^133*50000000000000^101 ≤ 27497232574841^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6350364093 10000000000 27497232574841 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453751593/5000000000 : ℝ)^133 ≤ (4242886715443/100000000000000 : ℝ)^101 := by
    have hnat : (453751593 : ℕ)^133*100000000000000^101 ≤ 4242886715443^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453751593 5000000000 4242886715443 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5058640829/10000000000 : ℝ)^133 ≤ (20381324058361/50000000000000 : ℝ)^101 := by
    have hnat : (5058640829 : ℕ)^133*50000000000000^101 ≤ 20381324058361^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058640829 10000000000 20381324058361 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6350364093/10000000000 : ℝ), (-453751593/5000000000 : ℝ), (5058640829/10000000000 : ℝ)] ![(27497232574841/50000000000000 : ℝ), (4242886715443/100000000000000 : ℝ), (20381324058361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6350364093/10000000000 : ℝ)|^133 ≤ (27497232574841/50000000000000 : ℝ)^101
        have hw : |(6350364093/10000000000 : ℝ)|=(6350364093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453751593/5000000000 : ℝ)|^133 ≤ (4242886715443/100000000000000 : ℝ)^101
        have hw : |(-453751593/5000000000 : ℝ)|=(453751593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5058640829/10000000000 : ℝ)|^133 ≤ (20381324058361/50000000000000 : ℝ)^101
        have hw : |(5058640829/10000000000 : ℝ)|=(5058640829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (904942959/2500000000 : ℝ)*x 0 + (169011553/250000000 : ℝ)*x 1 + (-563173883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904942959/2500000000 : ℝ)^133 ≤ (5246714262229/20000000000000 : ℝ)^101 := by
    have hnat : (904942959 : ℕ)^133*20000000000000^101 ≤ 5246714262229^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904942959 2500000000 5246714262229 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169011553/250000000 : ℝ)^133 ≤ (29859155431979/50000000000000 : ℝ)^101 := by
    have hnat : (169011553 : ℕ)^133*50000000000000^101 ≤ 29859155431979^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169011553 250000000 29859155431979 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563173883/2500000000 : ℝ)^133 ≤ (1756014725627/12500000000000 : ℝ)^101 := by
    have hnat : (563173883 : ℕ)^133*12500000000000^101 ≤ 1756014725627^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563173883 2500000000 1756014725627 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(904942959/2500000000 : ℝ), (169011553/250000000 : ℝ), (-563173883/2500000000 : ℝ)] ![(5246714262229/20000000000000 : ℝ), (29859155431979/50000000000000 : ℝ), (1756014725627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(904942959/2500000000 : ℝ)|^133 ≤ (5246714262229/20000000000000 : ℝ)^101
        have hw : |(904942959/2500000000 : ℝ)|=(904942959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169011553/250000000 : ℝ)|^133 ≤ (29859155431979/50000000000000 : ℝ)^101
        have hw : |(169011553/250000000 : ℝ)|=(169011553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563173883/2500000000 : ℝ)|^133 ≤ (1756014725627/12500000000000 : ℝ)^101
        have hw : |(-563173883/2500000000 : ℝ)|=(563173883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (307217837/1000000000 : ℝ)*x 0 + (604784433/1250000000 : ℝ)*x 1 + (5026494211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307217837/1000000000 : ℝ)^133 ≤ (4227496060799/20000000000000 : ℝ)^101 := by
    have hnat : (307217837 : ℕ)^133*20000000000000^101 ≤ 4227496060799^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307217837 1000000000 4227496060799 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604784433/1250000000 : ℝ)^133 ≤ (19220318697929/50000000000000 : ℝ)^101 := by
    have hnat : (604784433 : ℕ)^133*50000000000000^101 ≤ 19220318697929^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604784433 1250000000 19220318697929 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026494211/10000000000 : ℝ)^133 ≤ (40421882284861/100000000000000 : ℝ)^101 := by
    have hnat : (5026494211 : ℕ)^133*100000000000000^101 ≤ 40421882284861^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026494211 10000000000 40421882284861 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(307217837/1000000000 : ℝ), (604784433/1250000000 : ℝ), (5026494211/10000000000 : ℝ)] ![(4227496060799/20000000000000 : ℝ), (19220318697929/50000000000000 : ℝ), (40421882284861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(307217837/1000000000 : ℝ)|^133 ≤ (4227496060799/20000000000000 : ℝ)^101
        have hw : |(307217837/1000000000 : ℝ)|=(307217837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(604784433/1250000000 : ℝ)|^133 ≤ (19220318697929/50000000000000 : ℝ)^101
        have hw : |(604784433/1250000000 : ℝ)|=(604784433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026494211/10000000000 : ℝ)|^133 ≤ (40421882284861/100000000000000 : ℝ)^101
        have hw : |(5026494211/10000000000 : ℝ)|=(5026494211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-572072687/2500000000 : ℝ)*x 0 + (4434471069/10000000000 : ℝ)*x 1 + (6031370603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572072687/2500000000 : ℝ)^133 ≤ (717057637521/5000000000000 : ℝ)^101 := by
    have hnat : (572072687 : ℕ)^133*5000000000000^101 ≤ 717057637521^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572072687 2500000000 717057637521 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4434471069/10000000000 : ℝ)^133 ≤ (17136421326701/50000000000000 : ℝ)^101 := by
    have hnat : (4434471069 : ℕ)^133*50000000000000^101 ≤ 17136421326701^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434471069 10000000000 17136421326701 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6031370603/10000000000 : ℝ)^133 ≤ (25693002292793/50000000000000 : ℝ)^101 := by
    have hnat : (6031370603 : ℕ)^133*50000000000000^101 ≤ 25693002292793^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6031370603 10000000000 25693002292793 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-572072687/2500000000 : ℝ), (4434471069/10000000000 : ℝ), (6031370603/10000000000 : ℝ)] ![(717057637521/5000000000000 : ℝ), (17136421326701/50000000000000 : ℝ), (25693002292793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-572072687/2500000000 : ℝ)|^133 ≤ (717057637521/5000000000000 : ℝ)^101
        have hw : |(-572072687/2500000000 : ℝ)|=(572072687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4434471069/10000000000 : ℝ)|^133 ≤ (17136421326701/50000000000000 : ℝ)^101
        have hw : |(4434471069/10000000000 : ℝ)|=(4434471069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6031370603/10000000000 : ℝ)|^133 ≤ (25693002292793/50000000000000 : ℝ)^101
        have hw : |(6031370603/10000000000 : ℝ)|=(6031370603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7056095279/10000000000 : ℝ)*x 0 + (-95503159/625000000 : ℝ)*x 1 + (1921925557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7056095279/10000000000 : ℝ)^133 ≤ (63180760912553/100000000000000 : ℝ)^101 := by
    have hnat : (7056095279 : ℕ)^133*100000000000000^101 ≤ 63180760912553^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7056095279 10000000000 63180760912553 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95503159/625000000 : ℝ)^133 ≤ (1685297963667/20000000000000 : ℝ)^101 := by
    have hnat : (95503159 : ℕ)^133*20000000000000^101 ≤ 1685297963667^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95503159 625000000 1685297963667 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921925557/5000000000 : ℝ)^133 ≤ (3549093656949/12500000000000 : ℝ)^101 := by
    have hnat : (1921925557 : ℕ)^133*12500000000000^101 ≤ 3549093656949^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921925557 5000000000 3549093656949 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7056095279/10000000000 : ℝ), (-95503159/625000000 : ℝ), (1921925557/5000000000 : ℝ)] ![(63180760912553/100000000000000 : ℝ), (1685297963667/20000000000000 : ℝ), (3549093656949/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7056095279/10000000000 : ℝ)|^133 ≤ (63180760912553/100000000000000 : ℝ)^101
        have hw : |(7056095279/10000000000 : ℝ)|=(7056095279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95503159/625000000 : ℝ)|^133 ≤ (1685297963667/20000000000000 : ℝ)^101
        have hw : |(-95503159/625000000 : ℝ)|=(95503159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921925557/5000000000 : ℝ)|^133 ≤ (3549093656949/12500000000000 : ℝ)^101
        have hw : |(1921925557/5000000000 : ℝ)|=(1921925557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (126644547/312500000 : ℝ)*x 0 + (6341762797/10000000000 : ℝ)*x 1 + (-581792549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126644547/312500000 : ℝ)^133 ≤ (15220361380251/50000000000000 : ℝ)^101 := by
    have hnat : (126644547 : ℕ)^133*50000000000000^101 ≤ 15220361380251^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126644547 312500000 15220361380251 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6341762797/10000000000 : ℝ)^133 ≤ (27448199255113/50000000000000 : ℝ)^101 := by
    have hnat : (6341762797 : ℕ)^133*50000000000000^101 ≤ 27448199255113^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6341762797 10000000000 27448199255113 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (581792549/2500000000 : ℝ)^133 ≤ (1832859838691/12500000000000 : ℝ)^101 := by
    have hnat : (581792549 : ℕ)^133*12500000000000^101 ≤ 1832859838691^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581792549 2500000000 1832859838691 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126644547/312500000 : ℝ), (6341762797/10000000000 : ℝ), (-581792549/2500000000 : ℝ)] ![(15220361380251/50000000000000 : ℝ), (27448199255113/50000000000000 : ℝ), (1832859838691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126644547/312500000 : ℝ)|^133 ≤ (15220361380251/50000000000000 : ℝ)^101
        have hw : |(126644547/312500000 : ℝ)|=(126644547/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6341762797/10000000000 : ℝ)|^133 ≤ (27448199255113/50000000000000 : ℝ)^101
        have hw : |(6341762797/10000000000 : ℝ)|=(6341762797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-581792549/2500000000 : ℝ)|^133 ≤ (1832859838691/12500000000000 : ℝ)^101
        have hw : |(-581792549/2500000000 : ℝ)|=(581792549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3092378667/10000000000 : ℝ)*x 0 + (4302363027/10000000000 : ℝ)*x 1 + (34509813/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3092378667/10000000000 : ℝ)^133 ≤ (2132068907907/10000000000000 : ℝ)^101 := by
    have hnat : (3092378667 : ℕ)^133*10000000000000^101 ≤ 2132068907907^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092378667 10000000000 2132068907907 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4302363027/10000000000 : ℝ)^133 ≤ (16467354924177/50000000000000 : ℝ)^101 := by
    have hnat : (4302363027 : ℕ)^133*50000000000000^101 ≤ 16467354924177^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302363027 10000000000 16467354924177 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34509813/62500000 : ℝ)^133 ≤ (2859037566049/6250000000000 : ℝ)^101 := by
    have hnat : (34509813 : ℕ)^133*6250000000000^101 ≤ 2859037566049^101*62500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34509813 62500000 2859037566049 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3092378667/10000000000 : ℝ), (4302363027/10000000000 : ℝ), (34509813/62500000 : ℝ)] ![(2132068907907/10000000000000 : ℝ), (16467354924177/50000000000000 : ℝ), (2859037566049/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3092378667/10000000000 : ℝ)|^133 ≤ (2132068907907/10000000000000 : ℝ)^101
        have hw : |(3092378667/10000000000 : ℝ)|=(3092378667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4302363027/10000000000 : ℝ)|^133 ≤ (16467354924177/50000000000000 : ℝ)^101
        have hw : |(4302363027/10000000000 : ℝ)|=(4302363027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34509813/62500000 : ℝ)|^133 ≤ (2859037566049/6250000000000 : ℝ)^101
        have hw : |(34509813/62500000 : ℝ)|=(34509813/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-589555737/2500000000 : ℝ)*x 0 + (5346088299/10000000000 : ℝ)*x 1 + (637934383/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589555737/2500000000 : ℝ)^133 ≤ (14921066527157/100000000000000 : ℝ)^101 := by
    have hnat : (589555737 : ℕ)^133*100000000000000^101 ≤ 14921066527157^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589555737 2500000000 14921066527157 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5346088299/10000000000 : ℝ)^133 ≤ (43839879933783/100000000000000 : ℝ)^101 := by
    have hnat : (5346088299 : ℕ)^133*100000000000000^101 ≤ 43839879933783^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346088299 10000000000 43839879933783 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637934383/1250000000 : ℝ)^133 ≤ (10309763381453/25000000000000 : ℝ)^101 := by
    have hnat : (637934383 : ℕ)^133*25000000000000^101 ≤ 10309763381453^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637934383 1250000000 10309763381453 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-589555737/2500000000 : ℝ), (5346088299/10000000000 : ℝ), (637934383/1250000000 : ℝ)] ![(14921066527157/100000000000000 : ℝ), (43839879933783/100000000000000 : ℝ), (10309763381453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-589555737/2500000000 : ℝ)|^133 ≤ (14921066527157/100000000000000 : ℝ)^101
        have hw : |(-589555737/2500000000 : ℝ)|=(589555737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5346088299/10000000000 : ℝ)|^133 ≤ (43839879933783/100000000000000 : ℝ)^101
        have hw : |(5346088299/10000000000 : ℝ)|=(5346088299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637934383/1250000000 : ℝ)|^133 ≤ (10309763381453/25000000000000 : ℝ)^101
        have hw : |(637934383/1250000000 : ℝ)|=(637934383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3548553221/5000000000 : ℝ)*x 0 + (-122680557/1250000000 : ℝ)*x 1 + (1043110007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3548553221/5000000000 : ℝ)^133 ≤ (63664768230599/100000000000000 : ℝ)^101 := by
    have hnat : (3548553221 : ℕ)^133*100000000000000^101 ≤ 63664768230599^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548553221 5000000000 63664768230599 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122680557/1250000000 : ℝ)^133 ≤ (37631093139/800000000000 : ℝ)^101 := by
    have hnat : (122680557 : ℕ)^133*800000000000^101 ≤ 37631093139^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122680557 1250000000 37631093139 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043110007/2500000000 : ℝ)^133 ≤ (7907836278323/25000000000000 : ℝ)^101 := by
    have hnat : (1043110007 : ℕ)^133*25000000000000^101 ≤ 7907836278323^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043110007 2500000000 7907836278323 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3548553221/5000000000 : ℝ), (-122680557/1250000000 : ℝ), (1043110007/2500000000 : ℝ)] ![(63664768230599/100000000000000 : ℝ), (37631093139/800000000000 : ℝ), (7907836278323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3548553221/5000000000 : ℝ)|^133 ≤ (63664768230599/100000000000000 : ℝ)^101
        have hw : |(3548553221/5000000000 : ℝ)|=(3548553221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122680557/1250000000 : ℝ)|^133 ≤ (37631093139/800000000000 : ℝ)^101
        have hw : |(-122680557/1250000000 : ℝ)|=(122680557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043110007/2500000000 : ℝ)|^133 ≤ (7907836278323/25000000000000 : ℝ)^101
        have hw : |(1043110007/2500000000 : ℝ)|=(1043110007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (91467837/250000000 : ℝ)*x 0 + (781752039/1250000000 : ℝ)*x 1 + (-2889228657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91467837/250000000 : ℝ)^133 ≤ (5321168338081/20000000000000 : ℝ)^101 := by
    have hnat : (91467837 : ℕ)^133*20000000000000^101 ≤ 5321168338081^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91467837 250000000 5321168338081 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781752039/1250000000 : ℝ)^133 ≤ (53898381687903/100000000000000 : ℝ)^101 := by
    have hnat : (781752039 : ℕ)^133*100000000000000^101 ≤ 53898381687903^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781752039 1250000000 53898381687903 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2889228657/10000000000 : ℝ)^133 ≤ (389915532239/2000000000000 : ℝ)^101 := by
    have hnat : (2889228657 : ℕ)^133*2000000000000^101 ≤ 389915532239^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2889228657 10000000000 389915532239 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(91467837/250000000 : ℝ), (781752039/1250000000 : ℝ), (-2889228657/10000000000 : ℝ)] ![(5321168338081/20000000000000 : ℝ), (53898381687903/100000000000000 : ℝ), (389915532239/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(91467837/250000000 : ℝ)|^133 ≤ (5321168338081/20000000000000 : ℝ)^101
        have hw : |(91467837/250000000 : ℝ)|=(91467837/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781752039/1250000000 : ℝ)|^133 ≤ (53898381687903/100000000000000 : ℝ)^101
        have hw : |(781752039/1250000000 : ℝ)|=(781752039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2889228657/10000000000 : ℝ)|^133 ≤ (389915532239/2000000000000 : ℝ)^101
        have hw : |(-2889228657/10000000000 : ℝ)|=(2889228657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s3_s3_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1833890207/5000000000 : ℝ)*x 0 + (4750574581/10000000000 : ℝ)*x 1 + (1145485731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1833890207/5000000000 : ℝ)^133 ≤ (53385399327/200000000000 : ℝ)^101 := by
    have hnat : (1833890207 : ℕ)^133*200000000000^101 ≤ 53385399327^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833890207 5000000000 53385399327 200000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4750574581/10000000000 : ℝ)^133 ≤ (9381430918903/25000000000000 : ℝ)^101 := by
    have hnat : (4750574581 : ℕ)^133*25000000000000^101 ≤ 9381430918903^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750574581 10000000000 9381430918903 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145485731/2500000000 : ℝ)^133 ≤ (17890788323851/50000000000000 : ℝ)^101 := by
    have hnat : (1145485731 : ℕ)^133*50000000000000^101 ≤ 17890788323851^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145485731 2500000000 17890788323851 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1833890207/5000000000 : ℝ), (4750574581/10000000000 : ℝ), (1145485731/2500000000 : ℝ)] ![(53385399327/200000000000 : ℝ), (9381430918903/25000000000000 : ℝ), (17890788323851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1833890207/5000000000 : ℝ)|^133 ≤ (53385399327/200000000000 : ℝ)^101
        have hw : |(1833890207/5000000000 : ℝ)|=(1833890207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4750574581/10000000000 : ℝ)|^133 ≤ (9381430918903/25000000000000 : ℝ)^101
        have hw : |(4750574581/10000000000 : ℝ)|=(4750574581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145485731/2500000000 : ℝ)|^133 ≤ (17890788323851/50000000000000 : ℝ)^101
        have hw : |(1145485731/2500000000 : ℝ)|=(1145485731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304083_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((47801/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47801/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5631/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5631/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10493/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10493/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((21823/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(21823/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20683/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20683/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (47801/100000 : ℝ) ^ (33/8 : ℝ) ≤ (2380386923389403843/50000000000000000000 : ℝ) := by
    have hpowers : (47801/100000 : ℝ)^33 ≤ (2380386923389403843/50000000000000000000 : ℝ)^8 := by
      have hnat : (47801 : ℕ)^33*50000000000000000000^8 ≤ 2380386923389403843^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47801 100000 2380386923389403843 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47801/100000 : ℝ)) (X := (2380386923389403843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (52380386923389403843/50000000000000000000 : ℝ) ≤ (5056693822464637/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (52380386923389403843/50000000000000000000 : ℝ)^8 ≤ (5056693822464637/5000000000000000 : ℝ)^33 := by
      have hnat : (52380386923389403843 : ℕ)^8*5000000000000000^33 ≤ 5056693822464637^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52380386923389403843 50000000000000000000 5056693822464637 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056693822464637/5000000000000000 : ℝ)) (X := (52380386923389403843/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (27380386923389403843/25000000000000000000 : ℝ) ≤ (638933517616111/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (27380386923389403843/25000000000000000000 : ℝ)^8 ≤ (638933517616111/625000000000000 : ℝ)^33 := by
      have hnat : (27380386923389403843 : ℕ)^8*625000000000000^33 ≤ 638933517616111^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27380386923389403843 25000000000000000000 638933517616111 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638933517616111/625000000000000 : ℝ)) (X := (27380386923389403843/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(56693822464637/2390050000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(54774318464251/2390050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (47801/100000 : ℝ)) (alpha := (56693822464637/2390050000000000 : ℝ)) (beta := (54774318464251/2390050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (47801/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(56693822464637/2390050000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(54774318464251/2390050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (5631/12500 : ℝ) ^ (33/8 : ℝ) ≤ (931861792101568601/25000000000000000000 : ℝ) := by
    have hpowers : (5631/12500 : ℝ)^33 ≤ (931861792101568601/25000000000000000000 : ℝ)^8 := by
      have hnat : (5631 : ℕ)^33*25000000000000000000^8 ≤ 931861792101568601^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5631 12500 931861792101568601 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5631/12500 : ℝ)) (X := (931861792101568601/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (25931861792101568601/25000000000000000000 : ℝ) ≤ (5044556841770837/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25931861792101568601/25000000000000000000 : ℝ)^8 ≤ (5044556841770837/5000000000000000 : ℝ)^33 := by
      have hnat : (25931861792101568601 : ℕ)^8*5000000000000000^33 ≤ 5044556841770837^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25931861792101568601 25000000000000000000 5044556841770837 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044556841770837/5000000000000000 : ℝ)) (X := (25931861792101568601/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (13431861792101568601/12500000000000000000 : ℝ) ≤ (2035166680890237/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (13431861792101568601/12500000000000000000 : ℝ)^8 ≤ (2035166680890237/2000000000000000 : ℝ)^33 := by
      have hnat : (13431861792101568601 : ℕ)^8*2000000000000000^33 ≤ 2035166680890237^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13431861792101568601 12500000000000000000 2035166680890237 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2035166680890237/2000000000000000 : ℝ)) (X := (13431861792101568601/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14852280590279/750800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(86719720909511/4504800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (5631/12500 : ℝ)) (alpha := (14852280590279/750800000000000 : ℝ)) (beta := (86719720909511/4504800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (5631/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14852280590279/750800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(86719720909511/4504800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (10493/20000 : ℝ) ^ (33/8 : ℝ) ≤ (1397952496847085411/20000000000000000000 : ℝ) := by
    have hpowers : (10493/20000 : ℝ)^33 ≤ (1397952496847085411/20000000000000000000 : ℝ)^8 := by
      have hnat : (10493 : ℕ)^33*20000000000000000000^8 ≤ 1397952496847085411^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10493 20000 1397952496847085411 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10493/20000 : ℝ)) (X := (1397952496847085411/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (21397952496847085411/20000000000000000000 : ℝ) ≤ (10165137704211757/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (21397952496847085411/20000000000000000000 : ℝ)^8 ≤ (10165137704211757/10000000000000000 : ℝ)^33 := by
      have hnat : (21397952496847085411 : ℕ)^8*10000000000000000^33 ≤ 10165137704211757^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21397952496847085411 20000000000000000000 10165137704211757 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10165137704211757/10000000000000000 : ℝ)) (X := (21397952496847085411/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (11397952496847085411/10000000000000000000 : ℝ) ≤ (5161146759612177/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (11397952496847085411/10000000000000000000 : ℝ)^8 ≤ (5161146759612177/5000000000000000 : ℝ)^33 := by
      have hnat : (11397952496847085411 : ℕ)^8*5000000000000000^33 ≤ 5161146759612177^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11397952496847085411 10000000000000000000 5161146759612177 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5161146759612177/5000000000000000 : ℝ)) (X := (11397952496847085411/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(165137704211757/5246500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(157155815012597/5246500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (10493/20000 : ℝ)) (alpha := (165137704211757/5246500000000000 : ℝ)) (beta := (157155815012597/5246500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10493/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(165137704211757/5246500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(157155815012597/5246500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1403195383/5000000000 : ℝ)*X 0 0+(196264833/400000000 : ℝ)*X 0 1+(5182279653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((808747001/1250000000 : ℝ)*X 1 0+(-16149569/100000000 : ℝ)*X 1 1+(4464055623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((394382617/1000000000 : ℝ)*X 2 0+(3028508679/5000000000 : ℝ)*X 2 1+(-1414189169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-290686087/1000000000 : ℝ)*X 0 0+(4870454883/10000000000 : ℝ)*X 0 1+(16045381/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((6350364093/10000000000 : ℝ)*X 1 0+(-453751593/5000000000 : ℝ)*X 1 1+(5058640829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((904942959/2500000000 : ℝ)*X 2 0+(169011553/250000000 : ℝ)*X 2 1+(-563173883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((307217837/1000000000 : ℝ)*X 0 0+(604784433/1250000000 : ℝ)*X 0 1+(5026494211/10000000000 : ℝ)*X 0 2+(307217837/1000000000 : ℝ)*X 1 0+(604784433/1250000000 : ℝ)*X 1 1+(5026494211/10000000000 : ℝ)*X 1 2+(307217837/1000000000 : ℝ)*X 2 0+(604784433/1250000000 : ℝ)*X 2 1+(5026494211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-572072687/2500000000 : ℝ)*X 0 0+(4434471069/10000000000 : ℝ)*X 0 1+(6031370603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((7056095279/10000000000 : ℝ)*X 1 0+(-95503159/625000000 : ℝ)*X 1 1+(1921925557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((126644547/312500000 : ℝ)*X 2 0+(6341762797/10000000000 : ℝ)*X 2 1+(-581792549/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3092378667/10000000000 : ℝ)*X 0 0+(4302363027/10000000000 : ℝ)*X 0 1+(34509813/62500000 : ℝ)*X 0 2+(3092378667/10000000000 : ℝ)*X 1 0+(4302363027/10000000000 : ℝ)*X 1 1+(34509813/62500000 : ℝ)*X 1 2+(3092378667/10000000000 : ℝ)*X 2 0+(4302363027/10000000000 : ℝ)*X 2 1+(34509813/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-589555737/2500000000 : ℝ)*X 0 0+(5346088299/10000000000 : ℝ)*X 0 1+(637934383/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3548553221/5000000000 : ℝ)*X 1 0+(-122680557/1250000000 : ℝ)*X 1 1+(1043110007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((91467837/250000000 : ℝ)*X 2 0+(781752039/1250000000 : ℝ)*X 2 1+(-2889228657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1833890207/5000000000 : ℝ)*X 0 0+(4750574581/10000000000 : ℝ)*X 0 1+(1145485731/2500000000 : ℝ)*X 0 2+(1833890207/5000000000 : ℝ)*X 1 0+(4750574581/10000000000 : ℝ)*X 1 1+(1145485731/2500000000 : ℝ)*X 1 2+(1833890207/5000000000 : ℝ)*X 2 0+(4750574581/10000000000 : ℝ)*X 2 1+(1145485731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (241753319863573390490239871811/18829159023220000000000000000000000 : ℝ) := by norm_num
    linear_combination (70694242131/1000000000000 : ℝ)*(base40) + (1366679215129/1000000000000 : ℝ)*(base49) + (61581819157/200000000000 : ℝ)*(base60) + (265504442481/50000000000 : ℝ)*(major_s3_0) + (265504442481/50000000000 : ℝ)*(major_s3_1) + (265504442481/50000000000 : ℝ)*(major_s3_2) + (30900051/200000000000 : ℝ)*(sp_s3_0) + (91771071/250000000000 : ℝ)*(sp_s3_1) + (7118984549239/1000000000000 : ℝ)*(sp_s3_7) + (7118771965211/1000000000000 : ℝ)*(sp_s3_8) + (7118749478859/1000000000000 : ℝ)*(sp_s3_9) + (3501003634917/1000000000000 : ℝ)*(sp_s3_13) + (7683763/250000000000 : ℝ)*(sp_s3_20) + (77914127/200000000000 : ℝ)*(sp_s3_23) + (3501034369969/1000000000000 : ℝ)*(f.failure) + (3559569524747/500000000000 : ℝ)*(f.sum) + (2231331588995600813/3939072200000000000000000000000 : ℝ)*base62 + (165247386585977/262325000000000000000000000 : ℝ)*base65 + (19544590924531/37540000000000000000000000 : ℝ)*base67 + (157362259448851/524650000000000000000000000 : ℝ)*base68 + (2481019699503571193/3134849331250000000000000000000 : ℝ)*base71 + (92459794477987/239005000000000000000000000 : ℝ)*base72 + (1073960527781/75080000000000000000000000 : ℝ)*base74 + (56540494795237/59751250000000000000000000 : ℝ)*base77 + (616640719676847561/1794449540000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (7729/12500000000000000 : ℝ)*base86 + (7729/12500000000000000 : ℝ)*base88 + (7729/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((21823/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(21823/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17829967376124642435495340864997/1882915902322000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469437415939/500000000000 : ℝ)*(base40) + (152762822639/100000000000 : ℝ)*(base49) + (48408138093/62500000000 : ℝ)*(base60) + (6541296130379/1000000000000 : ℝ)*(major_s3_0) + (6541296130379/1000000000000 : ℝ)*(major_s3_1) + (6541296130379/1000000000000 : ℝ)*(major_s3_2) + (219028549/1000000000000 : ℝ)*(sp_s3_1) + (410493563/1000000000000 : ℝ)*(sp_s3_2) + (360956771/1000000000000 : ℝ)*(sp_s3_7) + (8769437302563/1000000000000 : ℝ)*(sp_s3_14) + (4384770599607/500000000000 : ℝ)*(sp_s3_15) + (2192346941443/250000000000 : ℝ)*(sp_s3_16) + (4312790844967/1000000000000 : ℝ)*(sp_s3_20) + (38031571/1000000000000 : ℝ)*(sp_s3_22) + (4312790844967/1000000000000 : ℝ)*(f.failure) + (1753959651867/200000000000 : ℝ)*(f.sum) + (87789148968174835259/236344332000000000000000000000000 : ℝ)*base63 + (2766344282871413/5246500000000000000000000000 : ℝ)*base65 + (619864129257221/750800000000000000000000000 : ℝ)*base67 + (5858874047305053/5246500000000000000000000000 : ℝ)*base69 + (35248172136741012003/250787946500000000000000000000000 : ℝ)*base71 + (409903857364137/1195025000000000000000000000 : ℝ)*base73 + (2349371053057571/4504800000000000000000000000 : ℝ)*base75 + (96985618071543/149378125000000000000000000 : ℝ)*base77 + (1419411858626725543/7177798160000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (8147/12500000000000000 : ℝ)*base86 + (8147/12500000000000000 : ℝ)*base88 + (8147/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20683/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20683/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (111278901709927514959654551/7177798160000000000000000000000 : ℝ) := by norm_num
    linear_combination (158125458427/200000000000 : ℝ)*(base40) + (1534878397427/1000000000000 : ℝ)*(base49) + (6737599/1000000000000 : ℝ)*(base50) + (1414797/500000000000 : ℝ)*(base60) + (6178830919803/1000000000000 : ℝ)*(major_s3_0) + (6178830919803/1000000000000 : ℝ)*(major_s3_1) + (6178830919803/1000000000000 : ℝ)*(major_s3_2) + (2578311/40000000000 : ℝ)*(sp_s3_2) + (121715863/1000000000000 : ℝ)*(sp_s3_15) + (70335893/500000000000 : ℝ)*(sp_s3_16) + (4141922737073/500000000000 : ℝ)*(sp_s3_21) + (8283723758283/1000000000000 : ℝ)*(sp_s3_22) + (4141820172293/500000000000 : ℝ)*(sp_s3_23) + (2036905598859/500000000000 : ℝ)*(sp_s3_27) + (2036905598859/500000000000 : ℝ)*(f.failure) + (4141922737073/500000000000 : ℝ)*(f.sum) + (48831889497909480279/78781444000000000000000000000000 : ℝ)*base62 + (123101808792591/5246500000000000000000000000 : ℝ)*base65 + (166114177227043/750800000000000000000000000 : ℝ)*base66 + (1077369729139121/5246500000000000000000000000 : ℝ)*base69 + (92009842060795989279/250787946500000000000000000000000 : ℝ)*base70 + (996489922976863/2390050000000000000000000000 : ℝ)*base73 + (1570762257510271/1501600000000000000000000000 : ℝ)*base74 + (2022553385775899/2390050000000000000000000000 : ℝ)*base76 + (2152130755825081913/7177798160000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (969/6250000000000000 : ℝ)*base86 + (969/6250000000000000 : ℝ)*base88 + (969/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((47801/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47801/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5631/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5631/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10493/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10493/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((21823/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(21823/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20683/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20683/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304083_s3 p hpa hpb X hX hprev2

#print axioms solution
