-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:33:29.504747+00:00
-- url     : https://prove2.me/submissions/ce4e4b7c-1956-40c1-bfef-f17a924bbaf6

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
theorem collision_support_c313055_s1_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1358575899/10000000000 : ℝ)*x 0 + (5872735783/10000000000 : ℝ)*x 1 + (5015322503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358575899/10000000000 : ℝ)^37 ≤ (3916558727267/50000000000000 : ℝ)^29 := by
    have hnat : (1358575899 : ℕ)^37*50000000000000^29 ≤ 3916558727267^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358575899 10000000000 3916558727267 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5872735783/10000000000 : ℝ)^37 ≤ (10141502673493/20000000000000 : ℝ)^29 := by
    have hnat : (5872735783 : ℕ)^37*20000000000000^29 ≤ 10141502673493^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872735783 10000000000 10141502673493 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015322503/10000000000 : ℝ)^37 ≤ (20729684584379/50000000000000 : ℝ)^29 := by
    have hnat : (5015322503 : ℕ)^37*50000000000000^29 ≤ 20729684584379^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015322503 10000000000 20729684584379 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1358575899/10000000000 : ℝ), (5872735783/10000000000 : ℝ), (5015322503/10000000000 : ℝ)] ![(3916558727267/50000000000000 : ℝ), (10141502673493/20000000000000 : ℝ), (20729684584379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1358575899/10000000000 : ℝ)|^37 ≤ (3916558727267/50000000000000 : ℝ)^29
        have hw : |(-1358575899/10000000000 : ℝ)|=(1358575899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5872735783/10000000000 : ℝ)|^37 ≤ (10141502673493/20000000000000 : ℝ)^29
        have hw : |(5872735783/10000000000 : ℝ)|=(5872735783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015322503/10000000000 : ℝ)|^37 ≤ (20729684584379/50000000000000 : ℝ)^29
        have hw : |(5015322503/10000000000 : ℝ)|=(5015322503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (243020573/500000000 : ℝ)*x 0 + (1511451283/2500000000 : ℝ)*x 1 + (-1319342669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243020573/500000000 : ℝ)^37 ≤ (39832540986219/100000000000000 : ℝ)^29 := by
    have hnat : (243020573 : ℕ)^37*100000000000000^29 ≤ 39832540986219^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243020573 500000000 39832540986219 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1511451283/2500000000 : ℝ)^37 ≤ (1644430998327/3125000000000 : ℝ)^29 := by
    have hnat : (1511451283 : ℕ)^37*3125000000000^29 ≤ 1644430998327^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511451283 2500000000 1644430998327 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319342669/10000000000 : ℝ)^37 ≤ (1886416762039/25000000000000 : ℝ)^29 := by
    have hnat : (1319342669 : ℕ)^37*25000000000000^29 ≤ 1886416762039^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319342669 10000000000 1886416762039 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(243020573/500000000 : ℝ), (1511451283/2500000000 : ℝ), (-1319342669/10000000000 : ℝ)] ![(39832540986219/100000000000000 : ℝ), (1644430998327/3125000000000 : ℝ), (1886416762039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(243020573/500000000 : ℝ)|^37 ≤ (39832540986219/100000000000000 : ℝ)^29
        have hw : |(243020573/500000000 : ℝ)|=(243020573/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1511451283/2500000000 : ℝ)|^37 ≤ (1644430998327/3125000000000 : ℝ)^29
        have hw : |(1511451283/2500000000 : ℝ)|=(1511451283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1319342669/10000000000 : ℝ)|^37 ≤ (1886416762039/25000000000000 : ℝ)^29
        have hw : |(-1319342669/10000000000 : ℝ)|=(1319342669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-462287061/2500000000 : ℝ)*x 0 + (874694349/2500000000 : ℝ)*x 1 + (6892851459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462287061/2500000000 : ℝ)^37 ≤ (2321598047021/20000000000000 : ℝ)^29 := by
    have hnat : (462287061 : ℕ)^37*20000000000000^29 ≤ 2321598047021^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462287061 2500000000 2321598047021 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874694349/2500000000 : ℝ)^37 ≤ (13093933370511/50000000000000 : ℝ)^29 := by
    have hnat : (874694349 : ℕ)^37*50000000000000^29 ≤ 13093933370511^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874694349 2500000000 13093933370511 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6892851459/10000000000 : ℝ)^37 ≤ (7775517875951/12500000000000 : ℝ)^29 := by
    have hnat : (6892851459 : ℕ)^37*12500000000000^29 ≤ 7775517875951^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6892851459 10000000000 7775517875951 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462287061/2500000000 : ℝ), (874694349/2500000000 : ℝ), (6892851459/10000000000 : ℝ)] ![(2321598047021/20000000000000 : ℝ), (13093933370511/50000000000000 : ℝ), (7775517875951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462287061/2500000000 : ℝ)|^37 ≤ (2321598047021/20000000000000 : ℝ)^29
        have hw : |(-462287061/2500000000 : ℝ)|=(462287061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874694349/2500000000 : ℝ)|^37 ≤ (13093933370511/50000000000000 : ℝ)^29
        have hw : |(874694349/2500000000 : ℝ)|=(874694349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6892851459/10000000000 : ℝ)|^37 ≤ (7775517875951/12500000000000 : ℝ)^29
        have hw : |(6892851459/10000000000 : ℝ)|=(6892851459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1553369443/5000000000 : ℝ)*x 0 + (-4767/10000000000 : ℝ)*x 1 + (8188812093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1553369443/5000000000 : ℝ)^37 ≤ (22503542616659/100000000000000 : ℝ)^29 := by
    have hnat : (1553369443 : ℕ)^37*100000000000000^29 ≤ 22503542616659^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553369443 5000000000 22503542616659 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4767/10000000000 : ℝ)^37 ≤ (859633/100000000000000 : ℝ)^29 := by
    have hnat : (4767 : ℕ)^37*100000000000000^29 ≤ 859633^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767 10000000000 859633 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8188812093/10000000000 : ℝ)^37 ≤ (15499291301367/20000000000000 : ℝ)^29 := by
    have hnat : (8188812093 : ℕ)^37*20000000000000^29 ≤ 15499291301367^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8188812093 10000000000 15499291301367 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1553369443/5000000000 : ℝ), (-4767/10000000000 : ℝ), (8188812093/10000000000 : ℝ)] ![(22503542616659/100000000000000 : ℝ), (859633/100000000000000 : ℝ), (15499291301367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1553369443/5000000000 : ℝ)|^37 ≤ (22503542616659/100000000000000 : ℝ)^29
        have hw : |(1553369443/5000000000 : ℝ)|=(1553369443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4767/10000000000 : ℝ)|^37 ≤ (859633/100000000000000 : ℝ)^29
        have hw : |(-4767/10000000000 : ℝ)|=(4767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8188812093/10000000000 : ℝ)|^37 ≤ (15499291301367/20000000000000 : ℝ)^29
        have hw : |(8188812093/10000000000 : ℝ)|=(8188812093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (154433357/500000000 : ℝ)*x 0 + (3908681011/5000000000 : ℝ)*x 1 + (-898727847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (154433357/500000000 : ℝ)^37 ≤ (22336663920759/100000000000000 : ℝ)^29 := by
    have hnat : (154433357 : ℕ)^37*100000000000000^29 ≤ 22336663920759^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154433357 500000000 22336663920759 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3908681011/5000000000 : ℝ)^37 ≤ (73039803628153/100000000000000 : ℝ)^29 := by
    have hnat : (3908681011 : ℕ)^37*100000000000000^29 ≤ 73039803628153^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3908681011 5000000000 73039803628153 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898727847/10000000000 : ℝ)^37 ≤ (924706486489/20000000000000 : ℝ)^29 := by
    have hnat : (898727847 : ℕ)^37*20000000000000^29 ≤ 924706486489^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898727847 10000000000 924706486489 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(154433357/500000000 : ℝ), (3908681011/5000000000 : ℝ), (-898727847/10000000000 : ℝ)] ![(22336663920759/100000000000000 : ℝ), (73039803628153/100000000000000 : ℝ), (924706486489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(154433357/500000000 : ℝ)|^37 ≤ (22336663920759/100000000000000 : ℝ)^29
        have hw : |(154433357/500000000 : ℝ)|=(154433357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3908681011/5000000000 : ℝ)|^37 ≤ (73039803628153/100000000000000 : ℝ)^29
        have hw : |(3908681011/5000000000 : ℝ)|=(3908681011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898727847/10000000000 : ℝ)|^37 ≤ (924706486489/20000000000000 : ℝ)^29
        have hw : |(-898727847/10000000000 : ℝ)|=(898727847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4177418339/10000000000 : ℝ)*x 0 + (3391939243/5000000000 : ℝ)*x 1 + (566493323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177418339/10000000000 : ℝ)^37 ≤ (16417266998841/50000000000000 : ℝ)^29 := by
    have hnat : (4177418339 : ℕ)^37*50000000000000^29 ≤ 16417266998841^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177418339 10000000000 16417266998841 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3391939243/5000000000 : ℝ)^37 ≤ (60952180852423/100000000000000 : ℝ)^29 := by
    have hnat : (3391939243 : ℕ)^37*100000000000000^29 ≤ 60952180852423^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3391939243 5000000000 60952180852423 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566493323/5000000000 : ℝ)^37 ≤ (3106642573149/50000000000000 : ℝ)^29 := by
    have hnat : (566493323 : ℕ)^37*50000000000000^29 ≤ 3106642573149^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566493323 5000000000 3106642573149 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177418339/10000000000 : ℝ), (3391939243/5000000000 : ℝ), (566493323/5000000000 : ℝ)] ![(16417266998841/50000000000000 : ℝ), (60952180852423/100000000000000 : ℝ), (3106642573149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177418339/10000000000 : ℝ)|^37 ≤ (16417266998841/50000000000000 : ℝ)^29
        have hw : |(4177418339/10000000000 : ℝ)|=(4177418339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3391939243/5000000000 : ℝ)|^37 ≤ (60952180852423/100000000000000 : ℝ)^29
        have hw : |(3391939243/5000000000 : ℝ)|=(3391939243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566493323/5000000000 : ℝ)|^37 ≤ (3106642573149/50000000000000 : ℝ)^29
        have hw : |(566493323/5000000000 : ℝ)|=(566493323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-64891181/1250000000 : ℝ)*x 0 + (408185201/1000000000 : ℝ)*x 1 + (7205422341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64891181/1250000000 : ℝ)^37 ≤ (2295455892837/100000000000000 : ℝ)^29 := by
    have hnat : (64891181 : ℕ)^37*100000000000000^29 ≤ 2295455892837^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64891181 1250000000 2295455892837 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408185201/1000000000 : ℝ)^37 ≤ (1992450541167/6250000000000 : ℝ)^29 := by
    have hnat : (408185201 : ℕ)^37*6250000000000^29 ≤ 1992450541167^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408185201 1000000000 1992450541167 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7205422341/10000000000 : ℝ)^37 ≤ (65825335436539/100000000000000 : ℝ)^29 := by
    have hnat : (7205422341 : ℕ)^37*100000000000000^29 ≤ 65825335436539^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7205422341 10000000000 65825335436539 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64891181/1250000000 : ℝ), (408185201/1000000000 : ℝ), (7205422341/10000000000 : ℝ)] ![(2295455892837/100000000000000 : ℝ), (1992450541167/6250000000000 : ℝ), (65825335436539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64891181/1250000000 : ℝ)|^37 ≤ (2295455892837/100000000000000 : ℝ)^29
        have hw : |(-64891181/1250000000 : ℝ)|=(64891181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(408185201/1000000000 : ℝ)|^37 ≤ (1992450541167/6250000000000 : ℝ)^29
        have hw : |(408185201/1000000000 : ℝ)|=(408185201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7205422341/10000000000 : ℝ)|^37 ≤ (65825335436539/100000000000000 : ℝ)^29
        have hw : |(7205422341/10000000000 : ℝ)|=(7205422341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2472647493/10000000000 : ℝ)*x 0 + (-1504279/31250000 : ℝ)*x 1 + (8485620927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2472647493/10000000000 : ℝ)^37 ≤ (336347863289/2000000000000 : ℝ)^29 := by
    have hnat : (2472647493 : ℕ)^37*2000000000000^29 ≤ 336347863289^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472647493 10000000000 336347863289 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1504279/31250000 : ℝ)^37 ≤ (260575837079/12500000000000 : ℝ)^29 := by
    have hnat : (1504279 : ℕ)^37*12500000000000^29 ≤ 260575837079^29*31250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504279 31250000 260575837079 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8485620927/10000000000 : ℝ)^37 ≤ (81098000125411/100000000000000 : ℝ)^29 := by
    have hnat : (8485620927 : ℕ)^37*100000000000000^29 ≤ 81098000125411^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8485620927 10000000000 81098000125411 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2472647493/10000000000 : ℝ), (-1504279/31250000 : ℝ), (8485620927/10000000000 : ℝ)] ![(336347863289/2000000000000 : ℝ), (260575837079/12500000000000 : ℝ), (81098000125411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2472647493/10000000000 : ℝ)|^37 ≤ (336347863289/2000000000000 : ℝ)^29
        have hw : |(2472647493/10000000000 : ℝ)|=(2472647493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1504279/31250000 : ℝ)|^37 ≤ (260575837079/12500000000000 : ℝ)^29
        have hw : |(-1504279/31250000 : ℝ)|=(1504279/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8485620927/10000000000 : ℝ)|^37 ≤ (81098000125411/100000000000000 : ℝ)^29
        have hw : |(8485620927/10000000000 : ℝ)|=(8485620927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7037152369/10000000000 : ℝ)*x 0 + (1073034903/2500000000 : ℝ)*x 1 + (-12285463/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7037152369/10000000000 : ℝ)^37 ≤ (63870389210371/100000000000000 : ℝ)^29 := by
    have hnat : (7037152369 : ℕ)^37*100000000000000^29 ≤ 63870389210371^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7037152369 10000000000 63870389210371 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073034903/2500000000 : ℝ)^37 ≤ (33989320738819/100000000000000 : ℝ)^29 := by
    have hnat : (1073034903 : ℕ)^37*100000000000000^29 ≤ 33989320738819^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073034903 2500000000 33989320738819 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12285463/250000000 : ℝ)^37 ≤ (107014501513/5000000000000 : ℝ)^29 := by
    have hnat : (12285463 : ℕ)^37*5000000000000^29 ≤ 107014501513^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12285463 250000000 107014501513 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7037152369/10000000000 : ℝ), (1073034903/2500000000 : ℝ), (-12285463/250000000 : ℝ)] ![(63870389210371/100000000000000 : ℝ), (33989320738819/100000000000000 : ℝ), (107014501513/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7037152369/10000000000 : ℝ)|^37 ≤ (63870389210371/100000000000000 : ℝ)^29
        have hw : |(7037152369/10000000000 : ℝ)|=(7037152369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1073034903/2500000000 : ℝ)|^37 ≤ (33989320738819/100000000000000 : ℝ)^29
        have hw : |(1073034903/2500000000 : ℝ)|=(1073034903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12285463/250000000 : ℝ)|^37 ≤ (107014501513/5000000000000 : ℝ)^29
        have hw : |(-12285463/250000000 : ℝ)|=(12285463/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4203167939/5000000000 : ℝ)*x 0 + (2462283611/10000000000 : ℝ)*x 1 + (663618503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203167939/5000000000 : ℝ)^37 ≤ (40066241240681/50000000000000 : ℝ)^29 := by
    have hnat : (4203167939 : ℕ)^37*50000000000000^29 ≤ 40066241240681^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203167939 5000000000 40066241240681 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2462283611/10000000000 : ℝ)^37 ≤ (1672751146971/10000000000000 : ℝ)^29 := by
    have hnat : (2462283611 : ℕ)^37*10000000000000^29 ≤ 1672751146971^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462283611 10000000000 1672751146971 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663618503/10000000000 : ℝ)^37 ≤ (3140006035121/100000000000000 : ℝ)^29 := by
    have hnat : (663618503 : ℕ)^37*100000000000000^29 ≤ 3140006035121^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663618503 10000000000 3140006035121 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203167939/5000000000 : ℝ), (2462283611/10000000000 : ℝ), (663618503/10000000000 : ℝ)] ![(40066241240681/50000000000000 : ℝ), (1672751146971/10000000000000 : ℝ), (3140006035121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203167939/5000000000 : ℝ)|^37 ≤ (40066241240681/50000000000000 : ℝ)^29
        have hw : |(4203167939/5000000000 : ℝ)|=(4203167939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2462283611/10000000000 : ℝ)|^37 ≤ (1672751146971/10000000000000 : ℝ)^29
        have hw : |(2462283611/10000000000 : ℝ)|=(2462283611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(663618503/10000000000 : ℝ)|^37 ≤ (3140006035121/100000000000000 : ℝ)^29
        have hw : |(663618503/10000000000 : ℝ)|=(663618503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-176991059/2000000000 : ℝ)*x 0 + (29279519/39062500 : ℝ)*x 1 + (3504342557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176991059/2000000000 : ℝ)^37 ≤ (4533325174573/100000000000000 : ℝ)^29 := by
    have hnat : (176991059 : ℕ)^37*100000000000000^29 ≤ 4533325174573^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176991059 2000000000 4533325174573 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29279519/39062500 : ℝ)^37 ≤ (8653206382737/12500000000000 : ℝ)^29 := by
    have hnat : (29279519 : ℕ)^37*12500000000000^29 ≤ 8653206382737^29*39062500^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29279519 39062500 8653206382737 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3504342557/10000000000 : ℝ)^37 ≤ (1312051187301/5000000000000 : ℝ)^29 := by
    have hnat : (3504342557 : ℕ)^37*5000000000000^29 ≤ 1312051187301^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3504342557 10000000000 1312051187301 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176991059/2000000000 : ℝ), (29279519/39062500 : ℝ), (3504342557/10000000000 : ℝ)] ![(4533325174573/100000000000000 : ℝ), (8653206382737/12500000000000 : ℝ), (1312051187301/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176991059/2000000000 : ℝ)|^37 ≤ (4533325174573/100000000000000 : ℝ)^29
        have hw : |(-176991059/2000000000 : ℝ)|=(176991059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29279519/39062500 : ℝ)|^37 ≤ (8653206382737/12500000000000 : ℝ)^29
        have hw : |(29279519/39062500 : ℝ)|=(29279519/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3504342557/10000000000 : ℝ)|^37 ≤ (1312051187301/5000000000000 : ℝ)^29
        have hw : |(3504342557/10000000000 : ℝ)|=(3504342557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1759481169/2500000000 : ℝ)*x 0 + (-3515179/2000000000 : ℝ)*x 1 + (449871209/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759481169/2500000000 : ℝ)^37 ≤ (31939666307493/50000000000000 : ℝ)^29 := by
    have hnat : (1759481169 : ℕ)^37*50000000000000^29 ≤ 31939666307493^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759481169 2500000000 31939666307493 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3515179/2000000000 : ℝ)^37 ≤ (7635450843/25000000000000 : ℝ)^29 := by
    have hnat : (3515179 : ℕ)^37*25000000000000^29 ≤ 7635450843^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3515179 2000000000 7635450843 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449871209/1000000000 : ℝ)^37 ≤ (18045062780987/50000000000000 : ℝ)^29 := by
    have hnat : (449871209 : ℕ)^37*50000000000000^29 ≤ 18045062780987^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449871209 1000000000 18045062780987 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1759481169/2500000000 : ℝ), (-3515179/2000000000 : ℝ), (449871209/1000000000 : ℝ)] ![(31939666307493/50000000000000 : ℝ), (7635450843/25000000000000 : ℝ), (18045062780987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1759481169/2500000000 : ℝ)|^37 ≤ (31939666307493/50000000000000 : ℝ)^29
        have hw : |(1759481169/2500000000 : ℝ)|=(1759481169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3515179/2000000000 : ℝ)|^37 ≤ (7635450843/25000000000000 : ℝ)^29
        have hw : |(-3515179/2000000000 : ℝ)|=(3515179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449871209/1000000000 : ℝ)|^37 ≤ (18045062780987/50000000000000 : ℝ)^29
        have hw : |(449871209/1000000000 : ℝ)|=(449871209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2115256299/10000000000 : ℝ)*x 0 + (2015075431/2500000000 : ℝ)*x 1 + (-1680115021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115256299/10000000000 : ℝ)^37 ≤ (13780222743341/100000000000000 : ℝ)^29 := by
    have hnat : (2115256299 : ℕ)^37*100000000000000^29 ≤ 13780222743341^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115256299 10000000000 13780222743341 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015075431/2500000000 : ℝ)^37 ≤ (9493518211707/12500000000000 : ℝ)^29 := by
    have hnat : (2015075431 : ℕ)^37*12500000000000^29 ≤ 9493518211707^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015075431 2500000000 9493518211707 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680115021/10000000000 : ℝ)^37 ≤ (10271631547007/100000000000000 : ℝ)^29 := by
    have hnat : (1680115021 : ℕ)^37*100000000000000^29 ≤ 10271631547007^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680115021 10000000000 10271631547007 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115256299/10000000000 : ℝ), (2015075431/2500000000 : ℝ), (-1680115021/10000000000 : ℝ)] ![(13780222743341/100000000000000 : ℝ), (9493518211707/12500000000000 : ℝ), (10271631547007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115256299/10000000000 : ℝ)|^37 ≤ (13780222743341/100000000000000 : ℝ)^29
        have hw : |(2115256299/10000000000 : ℝ)|=(2115256299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015075431/2500000000 : ℝ)|^37 ≤ (9493518211707/12500000000000 : ℝ)^29
        have hw : |(2015075431/2500000000 : ℝ)|=(2015075431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680115021/10000000000 : ℝ)|^37 ≤ (10271631547007/100000000000000 : ℝ)^29
        have hw : |(-1680115021/10000000000 : ℝ)|=(1680115021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4091240991/5000000000 : ℝ)*x 0 + (2095704059/10000000000 : ℝ)*x 1 + (754890503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4091240991/5000000000 : ℝ)^37 ≤ (77420032522781/100000000000000 : ℝ)^29 := by
    have hnat : (4091240991 : ℕ)^37*100000000000000^29 ≤ 77420032522781^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4091240991 5000000000 77420032522781 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095704059/10000000000 : ℝ)^37 ≤ (6808957697203/50000000000000 : ℝ)^29 := by
    have hnat : (2095704059 : ℕ)^37*50000000000000^29 ≤ 6808957697203^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095704059 10000000000 6808957697203 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754890503/5000000000 : ℝ)^37 ≤ (896205206987/10000000000000 : ℝ)^29 := by
    have hnat : (754890503 : ℕ)^37*10000000000000^29 ≤ 896205206987^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754890503 5000000000 896205206987 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4091240991/5000000000 : ℝ), (2095704059/10000000000 : ℝ), (754890503/5000000000 : ℝ)] ![(77420032522781/100000000000000 : ℝ), (6808957697203/50000000000000 : ℝ), (896205206987/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4091240991/5000000000 : ℝ)|^37 ≤ (77420032522781/100000000000000 : ℝ)^29
        have hw : |(4091240991/5000000000 : ℝ)|=(4091240991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2095704059/10000000000 : ℝ)|^37 ≤ (6808957697203/50000000000000 : ℝ)^29
        have hw : |(2095704059/10000000000 : ℝ)|=(2095704059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754890503/5000000000 : ℝ)|^37 ≤ (896205206987/10000000000000 : ℝ)^29
        have hw : |(754890503/5000000000 : ℝ)|=(754890503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313055_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20973/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20973/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3271/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3271/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82391/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82391/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33021/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33021/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65489/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65489/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (20973/25000 : ℝ) ^ (73/16 : ℝ) ≤ (44871955990644145677/100000000000000000000 : ℝ) := by
    have hpowers : (20973/25000 : ℝ)^73 ≤ (44871955990644145677/100000000000000000000 : ℝ)^16 := by
      have hnat : (20973 : ℕ)^73*100000000000000000000^16 ≤ 44871955990644145677^16*25000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20973 25000 44871955990644145677 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20973/25000 : ℝ)) (X := (44871955990644145677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (144871955990644145677/100000000000000000000 : ℝ) ≤ (5423182752288763/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (144871955990644145677/100000000000000000000 : ℝ)^16 ≤ (5423182752288763/5000000000000000 : ℝ)^73 := by
      have hnat : (144871955990644145677 : ℕ)^16*5000000000000000^73 ≤ 5423182752288763^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144871955990644145677 100000000000000000000 5423182752288763 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5423182752288763/5000000000000000 : ℝ)) (X := (144871955990644145677/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (94871955990644145677/50000000000000000000 : ℝ) ≤ (359598869409091/312500000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (94871955990644145677/50000000000000000000 : ℝ)^16 ≤ (359598869409091/312500000000000 : ℝ)^73 := by
      have hnat : (94871955990644145677 : ℕ)^16*312500000000000^73 ≤ 359598869409091^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94871955990644145677 50000000000000000000 359598869409091 312500000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (359598869409091/312500000000000 : ℝ)) (X := (94871955990644145677/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(423182752288763/4194600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(110133052752231/1398200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (20973/25000 : ℝ)) (alpha := (423182752288763/4194600000000000 : ℝ)) (beta := (110133052752231/1398200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20973/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(423182752288763/4194600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(110133052752231/1398200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3271/4000 : ℝ) ^ (73/16 : ℝ) ≤ (998323469003372761/2500000000000000000 : ℝ) := by
    have hpowers : (3271/4000 : ℝ)^73 ≤ (998323469003372761/2500000000000000000 : ℝ)^16 := by
      have hnat : (3271 : ℕ)^73*2500000000000000000^16 ≤ 998323469003372761^16*4000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3271 4000 998323469003372761 2500000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3271/4000 : ℝ)) (X := (998323469003372761/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3498323469003372761/2500000000000000000 : ℝ) ≤ (10764217287172929/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3498323469003372761/2500000000000000000 : ℝ)^16 ≤ (10764217287172929/10000000000000000 : ℝ)^73 := by
      have hnat : (3498323469003372761 : ℕ)^16*10000000000000000^73 ≤ 10764217287172929^73*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3498323469003372761 2500000000000000000 10764217287172929 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10764217287172929/10000000000000000 : ℝ)) (X := (3498323469003372761/2500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2248323469003372761/1250000000000000000 : ℝ) ≤ (11373108565172051/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2248323469003372761/1250000000000000000 : ℝ)^16 ≤ (11373108565172051/10000000000000000 : ℝ)^73 := by
      have hnat : (2248323469003372761 : ℕ)^16*10000000000000000^73 ≤ 11373108565172051^73*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2248323469003372761 1250000000000000000 11373108565172051 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11373108565172051/10000000000000000 : ℝ)) (X := (2248323469003372761/1250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(764217287172929/8177500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(304445638999561/4088750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (3271/4000 : ℝ)) (alpha := (764217287172929/8177500000000000 : ℝ)) (beta := (304445638999561/4088750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3271/4000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(764217287172929/8177500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(304445638999561/4088750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (82391/100000 : ℝ) ^ (73/16 : ℝ) ≤ (10330978974674958809/25000000000000000000 : ℝ) := by
    have hpowers : (82391/100000 : ℝ)^73 ≤ (10330978974674958809/25000000000000000000 : ℝ)^16 := by
      have hnat : (82391 : ℕ)^73*25000000000000000000^16 ≤ 10330978974674958809^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82391 100000 10330978974674958809 25000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82391/100000 : ℝ)) (X := (10330978974674958809/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (35330978974674958809/25000000000000000000 : ℝ) ≤ (5393789396661631/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (35330978974674958809/25000000000000000000 : ℝ)^16 ≤ (5393789396661631/5000000000000000 : ℝ)^73 := by
      have hnat : (35330978974674958809 : ℕ)^16*5000000000000000^73 ≤ 5393789396661631^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35330978974674958809 25000000000000000000 5393789396661631 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5393789396661631/5000000000000000 : ℝ)) (X := (35330978974674958809/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (22830978974674958809/12500000000000000000 : ℝ) ≤ (5705716293474627/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (22830978974674958809/12500000000000000000 : ℝ)^16 ≤ (5705716293474627/5000000000000000 : ℝ)^73 := by
      have hnat : (22830978974674958809 : ℕ)^16*5000000000000000^73 ≤ 5705716293474627^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22830978974674958809 12500000000000000000 5705716293474627 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5705716293474627/5000000000000000 : ℝ)) (X := (22830978974674958809/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(393789396661631/4119550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(77981724203249/1029887500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (82391/100000 : ℝ)) (alpha := (393789396661631/4119550000000000 : ℝ)) (beta := (77981724203249/1029887500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (82391/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(393789396661631/4119550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(77981724203249/1029887500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1358575899/10000000000 : ℝ)*X 0 0+(5872735783/10000000000 : ℝ)*X 0 1+(5015322503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((243020573/500000000 : ℝ)*X 2 0+(1511451283/2500000000 : ℝ)*X 2 1+(-1319342669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-462287061/2500000000 : ℝ)*X 0 0+(874694349/2500000000 : ℝ)*X 0 1+(6892851459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1553369443/5000000000 : ℝ)*X 1 0+(-4767/10000000000 : ℝ)*X 1 1+(8188812093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((154433357/500000000 : ℝ)*X 2 0+(3908681011/5000000000 : ℝ)*X 2 1+(-898727847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4177418339/10000000000 : ℝ)*X 0 0+(3391939243/5000000000 : ℝ)*X 0 1+(566493323/5000000000 : ℝ)*X 0 2+(4177418339/10000000000 : ℝ)*X 1 0+(3391939243/5000000000 : ℝ)*X 1 1+(566493323/5000000000 : ℝ)*X 1 2+(4177418339/10000000000 : ℝ)*X 2 0+(3391939243/5000000000 : ℝ)*X 2 1+(566493323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-64891181/1250000000 : ℝ)*X 0 0+(408185201/1000000000 : ℝ)*X 0 1+(7205422341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2472647493/10000000000 : ℝ)*X 1 0+(-1504279/31250000 : ℝ)*X 1 1+(8485620927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7037152369/10000000000 : ℝ)*X 2 0+(1073034903/2500000000 : ℝ)*X 2 1+(-12285463/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4203167939/5000000000 : ℝ)*X 0 0+(2462283611/10000000000 : ℝ)*X 0 1+(663618503/10000000000 : ℝ)*X 0 2+(4203167939/5000000000 : ℝ)*X 1 0+(2462283611/10000000000 : ℝ)*X 1 1+(663618503/10000000000 : ℝ)*X 1 2+(4203167939/5000000000 : ℝ)*X 2 0+(2462283611/10000000000 : ℝ)*X 2 1+(663618503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-176991059/2000000000 : ℝ)*X 0 0+(29279519/39062500 : ℝ)*X 0 1+(3504342557/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1759481169/2500000000 : ℝ)*X 1 0+(-3515179/2000000000 : ℝ)*X 1 1+(449871209/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2115256299/10000000000 : ℝ)*X 2 0+(2015075431/2500000000 : ℝ)*X 2 1+(-1680115021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4091240991/5000000000 : ℝ)*X 0 0+(2095704059/10000000000 : ℝ)*X 0 1+(754890503/5000000000 : ℝ)*X 0 2+(4091240991/5000000000 : ℝ)*X 1 0+(2095704059/10000000000 : ℝ)*X 1 1+(754890503/5000000000 : ℝ)*X 1 2+(4091240991/5000000000 : ℝ)*X 2 0+(2095704059/10000000000 : ℝ)*X 2 1+(754890503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((33021/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33021/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13146803954808746361863683624623/2355101522938750000000000000000000000 : ℝ) := by norm_num
    linear_combination (794933707373/1000000000000 : ℝ)*(base7) + (838081/1000000000000 : ℝ)*(base49) + (180669/500000000000 : ℝ)*(base53) + (302719/1000000000000 : ℝ)*(base60) + (1030003608951/500000000000 : ℝ)*(major_s1_0) + (1030003608951/500000000000 : ℝ)*(major_s1_1) + (515001714141/250000000000 : ℝ)*(major_s1_2) + (1623043/250000000000 : ℝ)*(sp_s1_0) + (2435618667261/1000000000000 : ℝ)*(sp_s1_7) + (487127231933/200000000000 : ℝ)*(sp_s1_8) + (2435631935317/1000000000000 : ℝ)*(sp_s1_9) + (402074083619/200000000000 : ℝ)*(sp_s1_13) + (1375029/125000000000 : ℝ)*(sp_s1_14) + (2292843/500000000000 : ℝ)*(sp_s1_23) + (607718355361/500000000000 : ℝ)*(f.failure) + (2435636521003/1000000000000 : ℝ)*(f.sum) + (6633891568246752941/84219050312500000000000000000000 : ℝ)*base63 + (1183136010625117/2059775000000000000000000000 : ℝ)*base65 + (3199412150785603/4088750000000000000000000000 : ℝ)*base67 + (1206587753038659/4119550000000000000000000000 : ℝ)*base69 + (24993207054779317019/57599548100000000000000000000000 : ℝ)*base71 + (334523274709031/699100000000000000000000000 : ℝ)*base73 + (869295398429427/2044375000000000000000000000 : ℝ)*base75 + (484689959148591/699100000000000000000000000 : ℝ)*base77 + (21076658005015027921/57168902500000000000000000000000 : ℝ)*base79 + (30193/50000000000000000 : ℝ)*base86 + (30193/50000000000000000 : ℝ)*base88 + (30193/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (929735372509332685613687577/84219050312500000000000000000000 : ℝ) := by norm_num
    linear_combination (164650246129/250000000000 : ℝ)*(base7) + (2833463/500000000000 : ℝ)*(base27) + (86053/1000000000000 : ℝ)*(base59) + (1823300121429/1000000000000 : ℝ)*(major_s1_0) + (1823300121429/1000000000000 : ℝ)*(major_s1_1) + (1823300121429/1000000000000 : ℝ)*(major_s1_2) + (3643413/200000000000 : ℝ)*(sp_s1_0) + (13265909/1000000000000 : ℝ)*(sp_s1_2) + (29217849/250000000000 : ℝ)*(sp_s1_8) + (87291489773/40000000000 : ℝ)*(sp_s1_14) + (2182188589993/1000000000000 : ℝ)*(sp_s1_15) + (54557304887/25000000000 : ℝ)*(sp_s1_16) + (346867006121/200000000000 : ℝ)*(sp_s1_20) + (18040921/500000000000 : ℝ)*(sp_s1_27) + (1075775794857/1000000000000 : ℝ)*(f.failure) + (218230546139/100000000000 : ℝ)*(f.sum) + (262301971273067780231/673752402500000000000000000000000 : ℝ)*base63 + (1568158051014103/2059775000000000000000000000 : ℝ)*base64 + (831181670494897/2044375000000000000000000000 : ℝ)*base66 + (521762100748727/2059775000000000000000000000 : ℝ)*base69 + (1352074040677539057/4607963848000000000000000000000 : ℝ)*base70 + (339675351305179/1398200000000000000000000000 : ℝ)*base73 + (3684438594677041/8177500000000000000000000000 : ℝ)*base75 + (11141947208689/1398200000000000000000000000 : ℝ)*base77 + (4883741310091953191/114337805000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (28359/100000000000000000 : ℝ)*base87 + (28359/100000000000000000 : ℝ)*base89 + (28359/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65489/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65489/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23204077795963289035185777/2879977405000000000000000000000 : ℝ) := by norm_num
    linear_combination (200726125929/250000000000 : ℝ)*(base7) + (5209/200000000000 : ℝ)*(base34) + (70305207651/1000000000000 : ℝ)*(base40) + (770441/500000000000 : ℝ)*(base43) + (299929/1000000000000 : ℝ)*(base59) + (222768953433/125000000000 : ℝ)*(major_s1_0) + (1782150112627/1000000000000 : ℝ)*(major_s1_1) + (1782151653509/1000000000000 : ℝ)*(major_s1_2) + (2483623/62500000000 : ℝ)*(sp_s1_9) + (20372363/1000000000000 : ℝ)*(sp_s1_20) + (509790027017/250000000000 : ℝ)*(sp_s1_21) + (407832334999/200000000000 : ℝ)*(sp_s1_22) + (407824079229/200000000000 : ℝ)*(sp_s1_23) + (1854381655863/1000000000000 : ℝ)*(sp_s1_27) + (210299510111/200000000000 : ℝ)*(f.failure) + (407832334999/200000000000 : ℝ)*(f.sum) + (114284353815214724303/673752402500000000000000000000000 : ℝ)*base63 + (1062508091507623/2059775000000000000000000000 : ℝ)*base64 + (294732485990843/1022187500000000000000000000 : ℝ)*base66 + (963785102830821/4119550000000000000000000000 : ℝ)*base68 + (281634560223355099/1151990962000000000000000000000 : ℝ)*base70 + (94899770162689/349550000000000000000000000 : ℝ)*base72 + (1392594961751767/8177500000000000000000000000 : ℝ)*base74 + (42342863393761/87387500000000000000000000 : ℝ)*base76 + (4009643901409695123/28584451250000000000000000000000 : ℝ)*base79 + (3057/20000000000000000 : ℝ)*base87 + (3057/20000000000000000 : ℝ)*base89 + (3057/20000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((20973/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20973/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3271/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3271/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82391/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82391/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33021/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33021/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65489/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65489/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313055_s1 p hpa hpb X hX hprev0

#print axioms solution
