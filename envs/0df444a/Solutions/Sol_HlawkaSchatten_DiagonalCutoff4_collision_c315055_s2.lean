-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:55.012299+00:00
-- url     : https://prove2.me/submissions/940a4656-39d7-44dd-9335-2c01784aedc2

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
theorem collision_support_c315055_s2_s2_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-31268371/156250000 : ℝ)*x 0 + (5598267833/10000000000 : ℝ)*x 1 + (297255979/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31268371/156250000 : ℝ)^19 ≤ (13030506331897/100000000000000 : ℝ)^15 := by
    have hnat : (31268371 : ℕ)^19*100000000000000^15 ≤ 13030506331897^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31268371 156250000 13030506331897 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598267833/10000000000 : ℝ)^19 ≤ (47958764321201/100000000000000 : ℝ)^15 := by
    have hnat : (5598267833 : ℕ)^19*100000000000000^15 ≤ 47958764321201^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598267833 10000000000 47958764321201 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297255979/625000000 : ℝ)^19 ≤ (39010729330781/100000000000000 : ℝ)^15 := by
    have hnat : (297255979 : ℕ)^19*100000000000000^15 ≤ 39010729330781^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297255979 625000000 39010729330781 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31268371/156250000 : ℝ), (5598267833/10000000000 : ℝ), (297255979/625000000 : ℝ)] ![(13030506331897/100000000000000 : ℝ), (47958764321201/100000000000000 : ℝ), (39010729330781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31268371/156250000 : ℝ)|^19 ≤ (13030506331897/100000000000000 : ℝ)^15
        have hw : |(-31268371/156250000 : ℝ)|=(31268371/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598267833/10000000000 : ℝ)|^19 ≤ (47958764321201/100000000000000 : ℝ)^15
        have hw : |(5598267833/10000000000 : ℝ)|=(5598267833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297255979/625000000 : ℝ)|^19 ≤ (39010729330781/100000000000000 : ℝ)^15
        have hw : |(297255979/625000000 : ℝ)|=(297255979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4741750931/10000000000 : ℝ)*x 0 + (2807562181/5000000000 : ℝ)*x 1 + (-1997050913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4741750931/10000000000 : ℝ)^19 ≤ (19430877149503/50000000000000 : ℝ)^15 := by
    have hnat : (4741750931 : ℕ)^19*50000000000000^15 ≤ 19430877149503^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4741750931 10000000000 19430877149503 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2807562181/5000000000 : ℝ)^19 ≤ (48141750799823/100000000000000 : ℝ)^15 := by
    have hnat : (2807562181 : ℕ)^19*100000000000000^15 ≤ 48141750799823^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807562181 5000000000 48141750799823 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997050913/10000000000 : ℝ)^19 ≤ (6498247441619/50000000000000 : ℝ)^15 := by
    have hnat : (1997050913 : ℕ)^19*50000000000000^15 ≤ 6498247441619^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997050913 10000000000 6498247441619 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4741750931/10000000000 : ℝ), (2807562181/5000000000 : ℝ), (-1997050913/10000000000 : ℝ)] ![(19430877149503/50000000000000 : ℝ), (48141750799823/100000000000000 : ℝ), (6498247441619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4741750931/10000000000 : ℝ)|^19 ≤ (19430877149503/50000000000000 : ℝ)^15
        have hw : |(4741750931/10000000000 : ℝ)|=(4741750931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2807562181/5000000000 : ℝ)|^19 ≤ (48141750799823/100000000000000 : ℝ)^15
        have hw : |(2807562181/5000000000 : ℝ)|=(2807562181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997050913/10000000000 : ℝ)|^19 ≤ (6498247441619/50000000000000 : ℝ)^15
        have hw : |(-1997050913/10000000000 : ℝ)|=(1997050913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (759032623/1250000000 : ℝ)*x 0 + (391305307/1000000000 : ℝ)*x 1 + (2396404929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (759032623/1250000000 : ℝ)^19 ≤ (26579524947031/50000000000000 : ℝ)^15 := by
    have hnat : (759032623 : ℕ)^19*50000000000000^15 ≤ 26579524947031^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759032623 1250000000 26579524947031 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391305307/1000000000 : ℝ)^19 ≤ (3808581741967/12500000000000 : ℝ)^15 := by
    have hnat : (391305307 : ℕ)^19*12500000000000^15 ≤ 3808581741967^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391305307 1000000000 3808581741967 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396404929/10000000000 : ℝ)^19 ≤ (8186148078787/50000000000000 : ℝ)^15 := by
    have hnat : (2396404929 : ℕ)^19*50000000000000^15 ≤ 8186148078787^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396404929 10000000000 8186148078787 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(759032623/1250000000 : ℝ), (391305307/1000000000 : ℝ), (2396404929/10000000000 : ℝ)] ![(26579524947031/50000000000000 : ℝ), (3808581741967/12500000000000 : ℝ), (8186148078787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(759032623/1250000000 : ℝ)|^19 ≤ (26579524947031/50000000000000 : ℝ)^15
        have hw : |(759032623/1250000000 : ℝ)|=(759032623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(391305307/1000000000 : ℝ)|^19 ≤ (3808581741967/12500000000000 : ℝ)^15
        have hw : |(391305307/1000000000 : ℝ)|=(391305307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2396404929/10000000000 : ℝ)|^19 ≤ (8186148078787/50000000000000 : ℝ)^15
        have hw : |(2396404929/10000000000 : ℝ)|=(2396404929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-106456117/625000000 : ℝ)*x 0 + (1587581/3200000 : ℝ)*x 1 + (5622510633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106456117/625000000 : ℝ)^19 ≤ (2124865411737/20000000000000 : ℝ)^15 := by
    have hnat : (106456117 : ℕ)^19*20000000000000^15 ≤ 2124865411737^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106456117 625000000 2124865411737 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1587581/3200000 : ℝ)^19 ≤ (4115369407693/10000000000000 : ℝ)^15 := by
    have hnat : (1587581 : ℕ)^19*10000000000000^15 ≤ 4115369407693^15*3200000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587581 3200000 4115369407693 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5622510633/10000000000 : ℝ)^19 ≤ (48221978846869/100000000000000 : ℝ)^15 := by
    have hnat : (5622510633 : ℕ)^19*100000000000000^15 ≤ 48221978846869^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622510633 10000000000 48221978846869 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106456117/625000000 : ℝ), (1587581/3200000 : ℝ), (5622510633/10000000000 : ℝ)] ![(2124865411737/20000000000000 : ℝ), (4115369407693/10000000000000 : ℝ), (48221978846869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106456117/625000000 : ℝ)|^19 ≤ (2124865411737/20000000000000 : ℝ)^15
        have hw : |(-106456117/625000000 : ℝ)|=(106456117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1587581/3200000 : ℝ)|^19 ≤ (4115369407693/10000000000000 : ℝ)^15
        have hw : |(1587581/3200000 : ℝ)|=(1587581/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5622510633/10000000000 : ℝ)|^19 ≤ (48221978846869/100000000000000 : ℝ)^15
        have hw : |(5622510633/10000000000 : ℝ)|=(5622510633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1154755383/2500000000 : ℝ)*x 0 + (-245099419/5000000000 : ℝ)*x 1 + (6700067631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1154755383/2500000000 : ℝ)^19 ≤ (37592105417959/100000000000000 : ℝ)^15 := by
    have hnat : (1154755383 : ℕ)^19*100000000000000^15 ≤ 37592105417959^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154755383 2500000000 37592105417959 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245099419/5000000000 : ℝ)^19 ≤ (438700585223/20000000000000 : ℝ)^15 := by
    have hnat : (245099419 : ℕ)^19*20000000000000^15 ≤ 438700585223^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245099419 5000000000 438700585223 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6700067631/10000000000 : ℝ)^19 ≤ (30107195819893/50000000000000 : ℝ)^15 := by
    have hnat : (6700067631 : ℕ)^19*50000000000000^15 ≤ 30107195819893^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6700067631 10000000000 30107195819893 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1154755383/2500000000 : ℝ), (-245099419/5000000000 : ℝ), (6700067631/10000000000 : ℝ)] ![(37592105417959/100000000000000 : ℝ), (438700585223/20000000000000 : ℝ), (30107195819893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1154755383/2500000000 : ℝ)|^19 ≤ (37592105417959/100000000000000 : ℝ)^15
        have hw : |(1154755383/2500000000 : ℝ)|=(1154755383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245099419/5000000000 : ℝ)|^19 ≤ (438700585223/20000000000000 : ℝ)^15
        have hw : |(-245099419/5000000000 : ℝ)|=(245099419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6700067631/10000000000 : ℝ)|^19 ≤ (30107195819893/50000000000000 : ℝ)^15
        have hw : |(6700067631/10000000000 : ℝ)|=(6700067631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1152283527/2500000000 : ℝ)*x 0 + (126271439/200000000 : ℝ)*x 1 + (-1178165299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1152283527/2500000000 : ℝ)^19 ≤ (18745103419453/50000000000000 : ℝ)^15 := by
    have hnat : (1152283527 : ℕ)^19*50000000000000^15 ≤ 18745103419453^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152283527 2500000000 18745103419453 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126271439/200000000 : ℝ)^19 ≤ (13962242559083/25000000000000 : ℝ)^15 := by
    have hnat : (126271439 : ℕ)^19*25000000000000^15 ≤ 13962242559083^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126271439 200000000 13962242559083 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1178165299/10000000000 : ℝ)^19 ≤ (333041145799/5000000000000 : ℝ)^15 := by
    have hnat : (1178165299 : ℕ)^19*5000000000000^15 ≤ 333041145799^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178165299 10000000000 333041145799 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1152283527/2500000000 : ℝ), (126271439/200000000 : ℝ), (-1178165299/10000000000 : ℝ)] ![(18745103419453/50000000000000 : ℝ), (13962242559083/25000000000000 : ℝ), (333041145799/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1152283527/2500000000 : ℝ)|^19 ≤ (18745103419453/50000000000000 : ℝ)^15
        have hw : |(1152283527/2500000000 : ℝ)|=(1152283527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126271439/200000000 : ℝ)|^19 ≤ (13962242559083/25000000000000 : ℝ)^15
        have hw : |(126271439/200000000 : ℝ)|=(126271439/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1178165299/10000000000 : ℝ)|^19 ≤ (333041145799/5000000000000 : ℝ)^15
        have hw : |(-1178165299/10000000000 : ℝ)|=(1178165299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2647241121/5000000000 : ℝ)*x 0 + (5599632281/10000000000 : ℝ)*x 1 + (254403547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647241121/5000000000 : ℝ)^19 ≤ (11171627255997/25000000000000 : ℝ)^15 := by
    have hnat : (2647241121 : ℕ)^19*25000000000000^15 ≤ 11171627255997^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647241121 5000000000 11171627255997 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5599632281/10000000000 : ℝ)^19 ≤ (4797357066249/10000000000000 : ℝ)^15 := by
    have hnat : (5599632281 : ℕ)^19*10000000000000^15 ≤ 4797357066249^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5599632281 10000000000 4797357066249 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254403547/2000000000 : ℝ)^19 ≤ (7339920300131/100000000000000 : ℝ)^15 := by
    have hnat : (254403547 : ℕ)^19*100000000000000^15 ≤ 7339920300131^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254403547 2000000000 7339920300131 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647241121/5000000000 : ℝ), (5599632281/10000000000 : ℝ), (254403547/2000000000 : ℝ)] ![(11171627255997/25000000000000 : ℝ), (4797357066249/10000000000000 : ℝ), (7339920300131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647241121/5000000000 : ℝ)|^19 ≤ (11171627255997/25000000000000 : ℝ)^15
        have hw : |(2647241121/5000000000 : ℝ)|=(2647241121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5599632281/10000000000 : ℝ)|^19 ≤ (4797357066249/10000000000000 : ℝ)^15
        have hw : |(5599632281/10000000000 : ℝ)|=(5599632281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254403547/2000000000 : ℝ)|^19 ≤ (7339920300131/100000000000000 : ℝ)^15
        have hw : |(254403547/2000000000 : ℝ)|=(254403547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-539462447/5000000000 : ℝ)*x 0 + (5295452049/10000000000 : ℝ)*x 1 + (572561741/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539462447/5000000000 : ℝ)^19 ≤ (5958297775553/100000000000000 : ℝ)^15 := by
    have hnat : (539462447 : ℕ)^19*100000000000000^15 ≤ 5958297775553^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539462447 5000000000 5958297775553 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5295452049/10000000000 : ℝ)^19 ≤ (44696877410893/100000000000000 : ℝ)^15 := by
    have hnat : (5295452049 : ℕ)^19*100000000000000^15 ≤ 44696877410893^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295452049 10000000000 44696877410893 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572561741/1000000000 : ℝ)^19 ≤ (49344824804993/100000000000000 : ℝ)^15 := by
    have hnat : (572561741 : ℕ)^19*100000000000000^15 ≤ 49344824804993^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572561741 1000000000 49344824804993 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539462447/5000000000 : ℝ), (5295452049/10000000000 : ℝ), (572561741/1000000000 : ℝ)] ![(5958297775553/100000000000000 : ℝ), (44696877410893/100000000000000 : ℝ), (49344824804993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539462447/5000000000 : ℝ)|^19 ≤ (5958297775553/100000000000000 : ℝ)^15
        have hw : |(-539462447/5000000000 : ℝ)|=(539462447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5295452049/10000000000 : ℝ)|^19 ≤ (44696877410893/100000000000000 : ℝ)^15
        have hw : |(5295452049/10000000000 : ℝ)|=(5295452049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572561741/1000000000 : ℝ)|^19 ≤ (49344824804993/100000000000000 : ℝ)^15
        have hw : |(572561741/1000000000 : ℝ)|=(572561741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (864084511/2000000000 : ℝ)*x 0 + (-97782781/1000000000 : ℝ)*x 1 + (669871319/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864084511/2000000000 : ℝ)^19 ≤ (6908173136741/20000000000000 : ℝ)^15 := by
    have hnat : (864084511 : ℕ)^19*20000000000000^15 ≤ 6908173136741^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864084511 2000000000 6908173136741 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97782781/1000000000 : ℝ)^19 ≤ (1315040200399/25000000000000 : ℝ)^15 := by
    have hnat : (97782781 : ℕ)^19*25000000000000^15 ≤ 1315040200399^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97782781 1000000000 1315040200399 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (669871319/1000000000 : ℝ)^19 ≤ (60198973504807/100000000000000 : ℝ)^15 := by
    have hnat : (669871319 : ℕ)^19*100000000000000^15 ≤ 60198973504807^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669871319 1000000000 60198973504807 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864084511/2000000000 : ℝ), (-97782781/1000000000 : ℝ), (669871319/1000000000 : ℝ)] ![(6908173136741/20000000000000 : ℝ), (1315040200399/25000000000000 : ℝ), (60198973504807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864084511/2000000000 : ℝ)|^19 ≤ (6908173136741/20000000000000 : ℝ)^15
        have hw : |(864084511/2000000000 : ℝ)|=(864084511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97782781/1000000000 : ℝ)|^19 ≤ (1315040200399/25000000000000 : ℝ)^15
        have hw : |(-97782781/1000000000 : ℝ)|=(97782781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(669871319/1000000000 : ℝ)|^19 ≤ (60198973504807/100000000000000 : ℝ)^15
        have hw : |(669871319/1000000000 : ℝ)|=(669871319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5711458671/10000000000 : ℝ)*x 0 + (2656213309/5000000000 : ℝ)*x 1 + (-537528167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5711458671/10000000000 : ℝ)^19 ≤ (12297578140223/25000000000000 : ℝ)^15 := by
    have hnat : (5711458671 : ℕ)^19*25000000000000^15 ≤ 12297578140223^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711458671 10000000000 12297578140223 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2656213309/5000000000 : ℝ)^19 ≤ (22439218810029/50000000000000 : ℝ)^15 := by
    have hnat : (2656213309 : ℕ)^19*50000000000000^15 ≤ 22439218810029^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656213309 5000000000 22439218810029 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537528167/5000000000 : ℝ)^19 ≤ (5931249797119/100000000000000 : ℝ)^15 := by
    have hnat : (537528167 : ℕ)^19*100000000000000^15 ≤ 5931249797119^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537528167 5000000000 5931249797119 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5711458671/10000000000 : ℝ), (2656213309/5000000000 : ℝ), (-537528167/5000000000 : ℝ)] ![(12297578140223/25000000000000 : ℝ), (22439218810029/50000000000000 : ℝ), (5931249797119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5711458671/10000000000 : ℝ)|^19 ≤ (12297578140223/25000000000000 : ℝ)^15
        have hw : |(5711458671/10000000000 : ℝ)|=(5711458671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2656213309/5000000000 : ℝ)|^19 ≤ (22439218810029/50000000000000 : ℝ)^15
        have hw : |(2656213309/5000000000 : ℝ)|=(2656213309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537528167/5000000000 : ℝ)|^19 ≤ (5931249797119/100000000000000 : ℝ)^15
        have hw : |(-537528167/5000000000 : ℝ)|=(537528167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3615281303/5000000000 : ℝ)*x 0 + (1742985767/5000000000 : ℝ)*x 1 + (318848253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3615281303/5000000000 : ℝ)^19 ≤ (33157973951807/50000000000000 : ℝ)^15 := by
    have hnat : (3615281303 : ℕ)^19*50000000000000^15 ≤ 33157973951807^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615281303 5000000000 33157973951807 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1742985767/5000000000 : ℝ)^19 ≤ (13159726511711/50000000000000 : ℝ)^15 := by
    have hnat : (1742985767 : ℕ)^19*50000000000000^15 ≤ 13159726511711^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742985767 5000000000 13159726511711 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318848253/2500000000 : ℝ)^19 ≤ (3682299533783/50000000000000 : ℝ)^15 := by
    have hnat : (318848253 : ℕ)^19*50000000000000^15 ≤ 3682299533783^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318848253 2500000000 3682299533783 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3615281303/5000000000 : ℝ), (1742985767/5000000000 : ℝ), (318848253/2500000000 : ℝ)] ![(33157973951807/50000000000000 : ℝ), (13159726511711/50000000000000 : ℝ), (3682299533783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3615281303/5000000000 : ℝ)|^19 ≤ (33157973951807/50000000000000 : ℝ)^15
        have hw : |(3615281303/5000000000 : ℝ)|=(3615281303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1742985767/5000000000 : ℝ)|^19 ≤ (13159726511711/50000000000000 : ℝ)^15
        have hw : |(1742985767/5000000000 : ℝ)|=(1742985767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318848253/2500000000 : ℝ)|^19 ≤ (3682299533783/50000000000000 : ℝ)^15
        have hw : |(318848253/2500000000 : ℝ)|=(318848253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-542945803/5000000000 : ℝ)*x 0 + (6190196083/10000000000 : ℝ)*x 1 + (192212353/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542945803/5000000000 : ℝ)^19 ≤ (1501768111519/25000000000000 : ℝ)^15 := by
    have hnat : (542945803 : ℕ)^19*25000000000000^15 ≤ 1501768111519^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542945803 5000000000 1501768111519 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6190196083/10000000000 : ℝ)^19 ≤ (54470193041937/100000000000000 : ℝ)^15 := by
    have hnat : (6190196083 : ℕ)^19*100000000000000^15 ≤ 54470193041937^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6190196083 10000000000 54470193041937 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192212353/400000000 : ℝ)^19 ≤ (39522734501239/100000000000000 : ℝ)^15 := by
    have hnat : (192212353 : ℕ)^19*100000000000000^15 ≤ 39522734501239^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192212353 400000000 39522734501239 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542945803/5000000000 : ℝ), (6190196083/10000000000 : ℝ), (192212353/400000000 : ℝ)] ![(1501768111519/25000000000000 : ℝ), (54470193041937/100000000000000 : ℝ), (39522734501239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542945803/5000000000 : ℝ)|^19 ≤ (1501768111519/25000000000000 : ℝ)^15
        have hw : |(-542945803/5000000000 : ℝ)|=(542945803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6190196083/10000000000 : ℝ)|^19 ≤ (54470193041937/100000000000000 : ℝ)^15
        have hw : |(6190196083/10000000000 : ℝ)|=(6190196083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192212353/400000000 : ℝ)|^19 ≤ (39522734501239/100000000000000 : ℝ)^15
        have hw : |(192212353/400000000 : ℝ)|=(192212353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5714378573/10000000000 : ℝ)*x 0 + (-454387741/10000000000 : ℝ)*x 1 + (1134859997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5714378573/10000000000 : ℝ)^19 ≤ (9844433734437/20000000000000 : ℝ)^15 := by
    have hnat : (5714378573 : ℕ)^19*20000000000000^15 ≤ 9844433734437^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714378573 10000000000 9844433734437 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454387741/10000000000 : ℝ)^19 ≤ (1992539934169/100000000000000 : ℝ)^15 := by
    have hnat : (454387741 : ℕ)^19*100000000000000^15 ≤ 1992539934169^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454387741 10000000000 1992539934169 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134859997/2000000000 : ℝ)^19 ≤ (24392645690991/50000000000000 : ℝ)^15 := by
    have hnat : (1134859997 : ℕ)^19*50000000000000^15 ≤ 24392645690991^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134859997 2000000000 24392645690991 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5714378573/10000000000 : ℝ), (-454387741/10000000000 : ℝ), (1134859997/2000000000 : ℝ)] ![(9844433734437/20000000000000 : ℝ), (1992539934169/100000000000000 : ℝ), (24392645690991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5714378573/10000000000 : ℝ)|^19 ≤ (9844433734437/20000000000000 : ℝ)^15
        have hw : |(5714378573/10000000000 : ℝ)|=(5714378573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454387741/10000000000 : ℝ)|^19 ≤ (1992539934169/100000000000000 : ℝ)^15
        have hw : |(-454387741/10000000000 : ℝ)|=(454387741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134859997/2000000000 : ℝ)|^19 ≤ (24392645690991/50000000000000 : ℝ)^15
        have hw : |(1134859997/2000000000 : ℝ)|=(1134859997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4251488879/10000000000 : ℝ)*x 0 + (1587345623/2500000000 : ℝ)*x 1 + (-1611611193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251488879/10000000000 : ℝ)^19 ≤ (16922141843163/50000000000000 : ℝ)^15 := by
    have hnat : (4251488879 : ℕ)^19*50000000000000^15 ≤ 16922141843163^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251488879 10000000000 16922141843163 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1587345623/2500000000 : ℝ)^19 ≤ (2812526081423/5000000000000 : ℝ)^15 := by
    have hnat : (1587345623 : ℕ)^19*5000000000000^15 ≤ 2812526081423^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587345623 2500000000 2812526081423 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1611611193/10000000000 : ℝ)^19 ≤ (309537333231/3125000000000 : ℝ)^15 := by
    have hnat : (1611611193 : ℕ)^19*3125000000000^15 ≤ 309537333231^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611611193 10000000000 309537333231 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251488879/10000000000 : ℝ), (1587345623/2500000000 : ℝ), (-1611611193/10000000000 : ℝ)] ![(16922141843163/50000000000000 : ℝ), (2812526081423/5000000000000 : ℝ), (309537333231/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251488879/10000000000 : ℝ)|^19 ≤ (16922141843163/50000000000000 : ℝ)^15
        have hw : |(4251488879/10000000000 : ℝ)|=(4251488879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1587345623/2500000000 : ℝ)|^19 ≤ (2812526081423/5000000000000 : ℝ)^15
        have hw : |(1587345623/2500000000 : ℝ)|=(1587345623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1611611193/10000000000 : ℝ)|^19 ≤ (309537333231/3125000000000 : ℝ)^15
        have hw : |(-1611611193/10000000000 : ℝ)|=(1611611193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315055_s2_s2_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (737777757/1000000000 : ℝ)*x 0 + (158468903/625000000 : ℝ)*x 1 + (2163551493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (737777757/1000000000 : ℝ)^19 ≤ (68030820112339/100000000000000 : ℝ)^15 := by
    have hnat : (737777757 : ℕ)^19*100000000000000^15 ≤ 68030820112339^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737777757 1000000000 68030820112339 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158468903/625000000 : ℝ)^19 ≤ (17585218814041/100000000000000 : ℝ)^15 := by
    have hnat : (158468903 : ℕ)^19*100000000000000^15 ≤ 17585218814041^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158468903 625000000 17585218814041 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163551493/10000000000 : ℝ)^19 ≤ (14383961066897/100000000000000 : ℝ)^15 := by
    have hnat : (2163551493 : ℕ)^19*100000000000000^15 ≤ 14383961066897^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163551493 10000000000 14383961066897 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(737777757/1000000000 : ℝ), (158468903/625000000 : ℝ), (2163551493/10000000000 : ℝ)] ![(68030820112339/100000000000000 : ℝ), (17585218814041/100000000000000 : ℝ), (14383961066897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(737777757/1000000000 : ℝ)|^19 ≤ (68030820112339/100000000000000 : ℝ)^15
        have hw : |(737777757/1000000000 : ℝ)|=(737777757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158468903/625000000 : ℝ)|^19 ≤ (17585218814041/100000000000000 : ℝ)^15
        have hw : |(158468903/625000000 : ℝ)|=(158468903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2163551493/10000000000 : ℝ)|^19 ≤ (14383961066897/100000000000000 : ℝ)^15
        have hw : |(2163551493/10000000000 : ℝ)|=(2163551493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315055_s2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((29969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5887/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5887/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29829/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2291/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2291/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36199/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36199/100000 : ℝ)*X 1 2) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (29969/50000 : ℝ) ^ (75/16 : ℝ) ≤ (9077772292312096193/100000000000000000000 : ℝ) := by
    have hpowers : (29969/50000 : ℝ)^75 ≤ (9077772292312096193/100000000000000000000 : ℝ)^16 := by
      have hnat : (29969 : ℕ)^75*100000000000000000000^16 ≤ 9077772292312096193^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29969 50000 9077772292312096193 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29969/50000 : ℝ)) (X := (9077772292312096193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (109077772292312096193/100000000000000000000 : ℝ) ≤ (5093548037997107/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (109077772292312096193/100000000000000000000 : ℝ)^16 ≤ (5093548037997107/5000000000000000 : ℝ)^75 := by
      have hnat : (109077772292312096193 : ℕ)^16*5000000000000000^75 ≤ 5093548037997107^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109077772292312096193 100000000000000000000 5093548037997107 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5093548037997107/5000000000000000 : ℝ)) (X := (109077772292312096193/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (59077772292312096193/50000000000000000000 : ℝ) ≤ (10362317049364161/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (59077772292312096193/50000000000000000000 : ℝ)^16 ≤ (10362317049364161/10000000000000000 : ℝ)^75 := by
      have hnat : (59077772292312096193 : ℕ)^16*10000000000000000^75 ≤ 10362317049364161^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59077772292312096193 50000000000000000000 10362317049364161 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10362317049364161/10000000000000000 : ℝ)) (X := (59077772292312096193/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(93548037997107/2996900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(175220973369947/5993800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (29969/50000 : ℝ)) (alpha := (93548037997107/2996900000000000 : ℝ)) (beta := (175220973369947/5993800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29969/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(93548037997107/2996900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(175220973369947/5993800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (5887/10000 : ℝ) ^ (75/16 : ℝ) ≤ (4172038401230738651/50000000000000000000 : ℝ) := by
    have hpowers : (5887/10000 : ℝ)^75 ≤ (4172038401230738651/50000000000000000000 : ℝ)^16 := by
      have hnat : (5887 : ℕ)^75*50000000000000000000^16 ≤ 4172038401230738651^16*10000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5887 10000 4172038401230738651 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5887/10000 : ℝ)) (X := (4172038401230738651/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (54172038401230738651/50000000000000000000 : ℝ) ≤ (2034487844017549/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (54172038401230738651/50000000000000000000 : ℝ)^16 ≤ (2034487844017549/2000000000000000 : ℝ)^75 := by
      have hnat : (54172038401230738651 : ℕ)^16*2000000000000000^75 ≤ 2034487844017549^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54172038401230738651 50000000000000000000 2034487844017549 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2034487844017549/2000000000000000 : ℝ)) (X := (54172038401230738651/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (29172038401230738651/25000000000000000000 : ℝ) ≤ (5167363915716393/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (29172038401230738651/25000000000000000000 : ℝ)^16 ≤ (5167363915716393/5000000000000000 : ℝ)^75 := by
      have hnat : (29172038401230738651 : ℕ)^16*5000000000000000^75 ≤ 5167363915716393^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29172038401230738651 25000000000000000000 5167363915716393 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5167363915716393/5000000000000000 : ℝ)) (X := (29172038401230738651/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(34487844017549/1177400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(162288611345041/5887000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (5887/10000 : ℝ)) (alpha := (34487844017549/1177400000000000 : ℝ)) (beta := (162288611345041/5887000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5887/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(34487844017549/1177400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(162288611345041/5887000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (29829/50000 : ℝ) ^ (75/16 : ℝ) ≤ (355227823385893399/4000000000000000000 : ℝ) := by
    have hpowers : (29829/50000 : ℝ)^75 ≤ (355227823385893399/4000000000000000000 : ℝ)^16 := by
      have hnat : (29829 : ℕ)^75*4000000000000000000^16 ≤ 355227823385893399^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29829 50000 355227823385893399 4000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29829/50000 : ℝ)) (X := (355227823385893399/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (4355227823385893399/4000000000000000000 : ℝ) ≤ (318223961232781/312500000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (4355227823385893399/4000000000000000000 : ℝ)^16 ≤ (318223961232781/312500000000000 : ℝ)^75 := by
      have hnat : (4355227823385893399 : ℕ)^16*312500000000000^75 ≤ 318223961232781^75*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4355227823385893399 4000000000000000000 318223961232781 312500000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (318223961232781/312500000000000 : ℝ)) (X := (4355227823385893399/4000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (2355227823385893399/2000000000000000000 : ℝ) ≤ (10354932952464327/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2355227823385893399/2000000000000000000 : ℝ)^16 ≤ (10354932952464327/10000000000000000 : ℝ)^75 := by
      have hnat : (2355227823385893399 : ℕ)^16*10000000000000000^75 ≤ 10354932952464327^75*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2355227823385893399 2000000000000000000 10354932952464327 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10354932952464327/10000000000000000 : ℝ)) (X := (2355227823385893399/2000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5723961232781/186431250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(34353238603067/1193160000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (29829/50000 : ℝ)) (alpha := (5723961232781/186431250000000 : ℝ)) (beta := (34353238603067/1193160000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29829/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5723961232781/186431250000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(34353238603067/1193160000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-31268371/156250000 : ℝ)*X 0 0+(5598267833/10000000000 : ℝ)*X 0 1+(297255979/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4741750931/10000000000 : ℝ)*X 2 0+(2807562181/5000000000 : ℝ)*X 2 1+(-1997050913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((759032623/1250000000 : ℝ)*X 0 0+(391305307/1000000000 : ℝ)*X 0 1+(2396404929/10000000000 : ℝ)*X 0 2+(759032623/1250000000 : ℝ)*X 1 0+(391305307/1000000000 : ℝ)*X 1 1+(2396404929/10000000000 : ℝ)*X 1 2+(759032623/1250000000 : ℝ)*X 2 0+(391305307/1000000000 : ℝ)*X 2 1+(2396404929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-106456117/625000000 : ℝ)*X 0 0+(1587581/3200000 : ℝ)*X 0 1+(5622510633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1154755383/2500000000 : ℝ)*X 1 0+(-245099419/5000000000 : ℝ)*X 1 1+(6700067631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1152283527/2500000000 : ℝ)*X 2 0+(126271439/200000000 : ℝ)*X 2 1+(-1178165299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2647241121/5000000000 : ℝ)*X 0 0+(5599632281/10000000000 : ℝ)*X 0 1+(254403547/2000000000 : ℝ)*X 0 2+(2647241121/5000000000 : ℝ)*X 1 0+(5599632281/10000000000 : ℝ)*X 1 1+(254403547/2000000000 : ℝ)*X 1 2+(2647241121/5000000000 : ℝ)*X 2 0+(5599632281/10000000000 : ℝ)*X 2 1+(254403547/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-539462447/5000000000 : ℝ)*X 0 0+(5295452049/10000000000 : ℝ)*X 0 1+(572561741/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((864084511/2000000000 : ℝ)*X 1 0+(-97782781/1000000000 : ℝ)*X 1 1+(669871319/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5711458671/10000000000 : ℝ)*X 2 0+(2656213309/5000000000 : ℝ)*X 2 1+(-537528167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3615281303/5000000000 : ℝ)*X 0 0+(1742985767/5000000000 : ℝ)*X 0 1+(318848253/2500000000 : ℝ)*X 0 2+(3615281303/5000000000 : ℝ)*X 1 0+(1742985767/5000000000 : ℝ)*X 1 1+(318848253/2500000000 : ℝ)*X 1 2+(3615281303/5000000000 : ℝ)*X 2 0+(1742985767/5000000000 : ℝ)*X 2 1+(318848253/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-542945803/5000000000 : ℝ)*X 0 0+(6190196083/10000000000 : ℝ)*X 0 1+(192212353/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5714378573/10000000000 : ℝ)*X 1 0+(-454387741/10000000000 : ℝ)*X 1 1+(1134859997/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4251488879/10000000000 : ℝ)*X 2 0+(1587345623/2500000000 : ℝ)*X 2 1+(-1611611193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((737777757/1000000000 : ℝ)*X 0 0+(158468903/625000000 : ℝ)*X 0 1+(2163551493/10000000000 : ℝ)*X 0 2+(737777757/1000000000 : ℝ)*X 1 0+(158468903/625000000 : ℝ)*X 1 1+(2163551493/10000000000 : ℝ)*X 1 2+(737777757/1000000000 : ℝ)*X 2 0+(158468903/625000000 : ℝ)*X 2 1+(2163551493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((35791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3996385951484920238641116930967/877109331164500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3257343/1000000000000 : ℝ)*(base19) + (127235336001/250000000000 : ℝ)*(base49) + (5245954939817/1000000000000 : ℝ)*(major_s2_0) + (5245954939817/1000000000000 : ℝ)*(major_s2_1) + (5245954939817/1000000000000 : ℝ)*(major_s2_2) + (12470993/1000000000000 : ℝ)*(sp_s2_0) + (1103097/1000000000000 : ℝ)*(sp_s2_6) + (1872087541119/250000000000 : ℝ)*(sp_s2_7) + (1872085904089/250000000000 : ℝ)*(sp_s2_8) + (23401015117/3125000000 : ℝ)*(sp_s2_9) + (1501770024207/500000000000 : ℝ)*(sp_s2_13) + (20335647/1000000000000 : ℝ)*(sp_s2_15) + (1143469/250000000000 : ℝ)*(sp_s2_21) + (21185953/500000000000 : ℝ)*(sp_s2_23) + (3003541151511/1000000000000 : ℝ)*(f.failure) + (1497673441869/200000000000 : ℝ)*(f.sum) + (1635700883790791387/7024132920000000000000000000000 : ℝ)*base62 + (175266903346577/1193160000000000000000000000 : ℝ)*base64 + (2807755801424403/5887000000000000000000000000 : ℝ)*base67 + (704125880439769/1491450000000000000000000000 : ℝ)*base68 + (18383247253058546363/178789060200000000000000000000000 : ℝ)*base70 + (4121426084659521/5993800000000000000000000000 : ℝ)*base72 + (680294923873667/1177400000000000000000000000 : ℝ)*base74 + (2097151786449021/2996900000000000000000000000 : ℝ)*base76 + (22508858752953726743/44106875750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (59749/100000000000000000 : ℝ)*base87 + (59749/100000000000000000 : ℝ)*base89 + (59749/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2291/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2291/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5770877176501944490069891569/1027060106750000000000000000000000 : ℝ) := by norm_num
    linear_combination (146823/200000000000 : ℝ)*(base39) + (12830347349/31250000000 : ℝ)*(base49) + (1171203/1000000000000 : ℝ)*(base60) + (2500311019213/500000000000 : ℝ)*(major_s2_0) + (2500311019213/500000000000 : ℝ)*(major_s2_1) + (2500311019213/500000000000 : ℝ)*(major_s2_2) + (19340461/1000000000000 : ℝ)*(sp_s2_2) + (2927761/100000000000 : ℝ)*(sp_s2_7) + (35625321/1000000000000 : ℝ)*(sp_s2_8) + (3569067854079/500000000000 : ℝ)*(sp_s2_14) + (7138129360447/1000000000000 : ℝ)*(sp_s2_15) + (7138145645307/1000000000000 : ℝ)*(sp_s2_16) + (2863047844161/1000000000000 : ℝ)*(sp_s2_20) + (3671747/125000000000 : ℝ)*(sp_s2_27) + (2863077218137/1000000000000 : ℝ)*(f.failure) + (892270623221/125000000000 : ℝ)*(f.sum) + (3108314240453977/8224980000000000000000000000 : ℝ)*base62 + (3704189356319/9780000000000000000000000 : ℝ)*base65 + (200833049047681/420500000000000000000000000 : ℝ)*base67 + (8619444804067/24450000000000000000000000 : ℝ)*base68 + (556741906797446753/1465484100000000000000000000000 : ℝ)*base71 + (640803086661821/2996900000000000000000000000 : ℝ)*base73 + (9187535349/84100000000000000000000000 : ℝ)*base74 + (9767963735441/1498450000000000000000000000 : ℝ)*base77 + (4140612472955968047/6300982250000000000000000000000 : ℝ)*base79 + (9717/100000000000000000 : ℝ)*base86 + (9717/100000000000000000 : ℝ)*base88 + (9717/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36199/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36199/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17492343107527011280209161/2926722050000000000000000000000 : ℝ) := by norm_num
    linear_combination (19575326467/200000000000 : ℝ)*(base40) + (105520942787/250000000000 : ℝ)*(base49) + (2706393/1000000000000 : ℝ)*(base59) + (30133627451/6250000000 : ℝ)*(major_s2_0) + (30133627451/6250000000 : ℝ)*(major_s2_1) + (30133627451/6250000000 : ℝ)*(major_s2_2) + (3332367/250000000000 : ℝ)*(sp_s2_0) + (13235299/1000000000000 : ℝ)*(sp_s2_2) + (5970397/500000000000 : ℝ)*(sp_s2_9) + (47990357/1000000000000 : ℝ)*(sp_s2_20) + (6882292012061/1000000000000 : ℝ)*(sp_s2_21) + (6882305341529/1000000000000 : ℝ)*(sp_s2_22) + (1720570041359/250000000000 : ℝ)*(sp_s2_23) + (690101365043/250000000000 : ℝ)*(sp_s2_27) + (2760453450529/1000000000000 : ℝ)*(f.failure) + (6882305341529/1000000000000 : ℝ)*(f.sum) + (16631563676540231/219504153750000000000000000000 : ℝ)*base63 + (23171459979451/298290000000000000000000000 : ℝ)*base65 + (7984237530223/294350000000000000000000000 : ℝ)*base66 + (27235622528093/59658000000000000000000000 : ℝ)*base69 + (1976100735767555437/8939453010000000000000000000000 : ℝ)*base70 + (90503126944271/299690000000000000000000000 : ℝ)*base73 + (26614063032203/58870000000000000000000000 : ℝ)*base75 + (11416630211761/18730625000000000000000000 : ℝ)*base77 + (4464130617581102257/8821375150000000000000000000000 : ℝ)*base78 + (55389/100000000000000000 : ℝ)*base86 + (55389/100000000000000000 : ℝ)*base88 + (55389/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((29969/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29969/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5887/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5887/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29829/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29829/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2291/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2291/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36199/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36199/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315055_s2 p hpa hpb X hX hprev1

#print axioms solution
