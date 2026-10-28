-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304063_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:39.157687+00:00
-- url     : https://prove2.me/submissions/4597585d-2720-4541-951c-3b6ca1e9d0bd

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
theorem collision_support_c304063_s5_s5_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-254811937/2500000000 : ℝ)*x 0 + (87623881/156250000 : ℝ)*x 1 + (2880164237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254811937/2500000000 : ℝ)^133 ≤ (494391924031/10000000000000 : ℝ)^101 := by
    have hnat : (254811937 : ℕ)^133*10000000000000^101 ≤ 494391924031^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254811937 2500000000 494391924031 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87623881/156250000 : ℝ)^133 ≤ (23344529397103/50000000000000 : ℝ)^101 := by
    have hnat : (87623881 : ℕ)^133*50000000000000^101 ≤ 23344529397103^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87623881 156250000 23344529397103 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2880164237/5000000000 : ℝ)^133 ≤ (1934680877879/4000000000000 : ℝ)^101 := by
    have hnat : (2880164237 : ℕ)^133*4000000000000^101 ≤ 1934680877879^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2880164237 5000000000 1934680877879 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254811937/2500000000 : ℝ), (87623881/156250000 : ℝ), (2880164237/5000000000 : ℝ)] ![(494391924031/10000000000000 : ℝ), (23344529397103/50000000000000 : ℝ), (1934680877879/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254811937/2500000000 : ℝ)|^133 ≤ (494391924031/10000000000000 : ℝ)^101
        have hw : |(-254811937/2500000000 : ℝ)|=(254811937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(87623881/156250000 : ℝ)|^133 ≤ (23344529397103/50000000000000 : ℝ)^101
        have hw : |(87623881/156250000 : ℝ)|=(87623881/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2880164237/5000000000 : ℝ)|^133 ≤ (1934680877879/4000000000000 : ℝ)^101
        have hw : |(2880164237/5000000000 : ℝ)|=(2880164237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5608620681/10000000000 : ℝ)*x 0 + (-1030182681/10000000000 : ℝ)*x 1 + (5753313033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5608620681/10000000000 : ℝ)^133 ≤ (11674162207701/25000000000000 : ℝ)^101 := by
    have hnat : (5608620681 : ℕ)^133*25000000000000^101 ≤ 11674162207701^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608620681 10000000000 11674162207701 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030182681/10000000000 : ℝ)^133 ≤ (1253470772141/25000000000000 : ℝ)^101 := by
    have hnat : (1030182681 : ℕ)^133*25000000000000^101 ≤ 1253470772141^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030182681 10000000000 1253470772141 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5753313033/10000000000 : ℝ)^133 ≤ (9657893613713/20000000000000 : ℝ)^101 := by
    have hnat : (5753313033 : ℕ)^133*20000000000000^101 ≤ 9657893613713^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5753313033 10000000000 9657893613713 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5608620681/10000000000 : ℝ), (-1030182681/10000000000 : ℝ), (5753313033/10000000000 : ℝ)] ![(11674162207701/25000000000000 : ℝ), (1253470772141/25000000000000 : ℝ), (9657893613713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5608620681/10000000000 : ℝ)|^133 ≤ (11674162207701/25000000000000 : ℝ)^101
        have hw : |(5608620681/10000000000 : ℝ)|=(5608620681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030182681/10000000000 : ℝ)|^133 ≤ (1253470772141/25000000000000 : ℝ)^101
        have hw : |(-1030182681/10000000000 : ℝ)|=(1030182681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5753313033/10000000000 : ℝ)|^133 ≤ (9657893613713/20000000000000 : ℝ)^101
        have hw : |(5753313033/10000000000 : ℝ)|=(5753313033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5669276621/10000000000 : ℝ)*x 0 + (5730452247/10000000000 : ℝ)*x 1 + (-482489181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5669276621/10000000000 : ℝ)^133 ≤ (23681401568287/50000000000000 : ℝ)^101 := by
    have hnat : (5669276621 : ℕ)^133*50000000000000^101 ≤ 23681401568287^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669276621 10000000000 23681401568287 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5730452247/10000000000 : ℝ)^133 ≤ (48036956002503/100000000000000 : ℝ)^101 := by
    have hnat : (5730452247 : ℕ)^133*100000000000000^101 ≤ 48036956002503^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5730452247 10000000000 48036956002503 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482489181/5000000000 : ℝ)^133 ≤ (575030105007/12500000000000 : ℝ)^101 := by
    have hnat : (482489181 : ℕ)^133*12500000000000^101 ≤ 575030105007^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482489181 5000000000 575030105007 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5669276621/10000000000 : ℝ), (5730452247/10000000000 : ℝ), (-482489181/5000000000 : ℝ)] ![(23681401568287/50000000000000 : ℝ), (48036956002503/100000000000000 : ℝ), (575030105007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5669276621/10000000000 : ℝ)|^133 ≤ (23681401568287/50000000000000 : ℝ)^101
        have hw : |(5669276621/10000000000 : ℝ)|=(5669276621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5730452247/10000000000 : ℝ)|^133 ≤ (48036956002503/100000000000000 : ℝ)^101
        have hw : |(5730452247/10000000000 : ℝ)|=(5730452247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482489181/5000000000 : ℝ)|^133 ≤ (575030105007/12500000000000 : ℝ)^101
        have hw : |(-482489181/5000000000 : ℝ)|=(482489181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4517928111/10000000000 : ℝ)*x 0 + (4367985057/10000000000 : ℝ)*x 1 + (2068471467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4517928111/10000000000 : ℝ)^133 ≤ (137206028491/390625000000 : ℝ)^101 := by
    have hnat : (4517928111 : ℕ)^133*390625000000^101 ≤ 137206028491^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517928111 10000000000 137206028491 390625000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4367985057/10000000000 : ℝ)^133 ≤ (33597797898091/100000000000000 : ℝ)^101 := by
    have hnat : (4367985057 : ℕ)^133*100000000000000^101 ≤ 33597797898091^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367985057 10000000000 33597797898091 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068471467/5000000000 : ℝ)^133 ≤ (15638729393931/50000000000000 : ℝ)^101 := by
    have hnat : (2068471467 : ℕ)^133*50000000000000^101 ≤ 15638729393931^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068471467 5000000000 15638729393931 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4517928111/10000000000 : ℝ), (4367985057/10000000000 : ℝ), (2068471467/5000000000 : ℝ)] ![(137206028491/390625000000 : ℝ), (33597797898091/100000000000000 : ℝ), (15638729393931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4517928111/10000000000 : ℝ)|^133 ≤ (137206028491/390625000000 : ℝ)^101
        have hw : |(4517928111/10000000000 : ℝ)|=(4517928111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4367985057/10000000000 : ℝ)|^133 ≤ (33597797898091/100000000000000 : ℝ)^101
        have hw : |(4367985057/10000000000 : ℝ)|=(4367985057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068471467/5000000000 : ℝ)|^133 ≤ (15638729393931/50000000000000 : ℝ)^101
        have hw : |(2068471467/5000000000 : ℝ)|=(2068471467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-217439477/2500000000 : ℝ)*x 0 + (163545767/400000000 : ℝ)*x 1 + (289035799/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217439477/2500000000 : ℝ)^133 ≤ (4012048659273/100000000000000 : ℝ)^101 := by
    have hnat : (217439477 : ℕ)^133*100000000000000^101 ≤ 4012048659273^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217439477 2500000000 4012048659273 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163545767/400000000 : ℝ)^133 ≤ (615949820987/2000000000000 : ℝ)^101 := by
    have hnat : (163545767 : ℕ)^133*2000000000000^101 ≤ 615949820987^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163545767 400000000 615949820987 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289035799/400000000 : ℝ)^133 ≤ (65190460277761/100000000000000 : ℝ)^101 := by
    have hnat : (289035799 : ℕ)^133*100000000000000^101 ≤ 65190460277761^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289035799 400000000 65190460277761 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217439477/2500000000 : ℝ), (163545767/400000000 : ℝ), (289035799/400000000 : ℝ)] ![(4012048659273/100000000000000 : ℝ), (615949820987/2000000000000 : ℝ), (65190460277761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217439477/2500000000 : ℝ)|^133 ≤ (4012048659273/100000000000000 : ℝ)^101
        have hw : |(-217439477/2500000000 : ℝ)|=(217439477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163545767/400000000 : ℝ)|^133 ≤ (615949820987/2000000000000 : ℝ)^101
        have hw : |(163545767/400000000 : ℝ)|=(163545767/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289035799/400000000 : ℝ)|^133 ≤ (65190460277761/100000000000000 : ℝ)^101
        have hw : |(289035799/400000000 : ℝ)|=(289035799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4449352151/10000000000 : ℝ)*x 0 + (-86074223/5000000000 : ℝ)*x 1 + (7218305479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4449352151/10000000000 : ℝ)^133 ≤ (34424374430029/100000000000000 : ℝ)^101 := by
    have hnat : (4449352151 : ℕ)^133*100000000000000^101 ≤ 34424374430029^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449352151 10000000000 34424374430029 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86074223/5000000000 : ℝ)^133 ≤ (237657389823/50000000000000 : ℝ)^101 := by
    have hnat : (86074223 : ℕ)^133*50000000000000^101 ≤ 237657389823^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86074223 5000000000 237657389823 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7218305479/10000000000 : ℝ)^133 ≤ (13020062155581/20000000000000 : ℝ)^101 := by
    have hnat : (7218305479 : ℕ)^133*20000000000000^101 ≤ 13020062155581^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7218305479 10000000000 13020062155581 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4449352151/10000000000 : ℝ), (-86074223/5000000000 : ℝ), (7218305479/10000000000 : ℝ)] ![(34424374430029/100000000000000 : ℝ), (237657389823/50000000000000 : ℝ), (13020062155581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4449352151/10000000000 : ℝ)|^133 ≤ (34424374430029/100000000000000 : ℝ)^101
        have hw : |(4449352151/10000000000 : ℝ)|=(4449352151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86074223/5000000000 : ℝ)|^133 ≤ (237657389823/50000000000000 : ℝ)^101
        have hw : |(-86074223/5000000000 : ℝ)|=(86074223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7218305479/10000000000 : ℝ)|^133 ≤ (13020062155581/20000000000000 : ℝ)^101
        have hw : |(7218305479/10000000000 : ℝ)|=(7218305479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1042965953/2500000000 : ℝ)*x 0 + (1871168159/2500000000 : ℝ)*x 1 + (-24798763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042965953/2500000000 : ℝ)^133 ≤ (15812796458907/50000000000000 : ℝ)^101 := by
    have hnat : (1042965953 : ℕ)^133*50000000000000^101 ≤ 15812796458907^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042965953 2500000000 15812796458907 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1871168159/2500000000 : ℝ)^133 ≤ (17070521080189/25000000000000 : ℝ)^101 := by
    have hnat : (1871168159 : ℕ)^133*25000000000000^101 ≤ 17070521080189^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871168159 2500000000 17070521080189 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24798763/5000000000 : ℝ)^133 ≤ (92322749733/100000000000000 : ℝ)^101 := by
    have hnat : (24798763 : ℕ)^133*100000000000000^101 ≤ 92322749733^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24798763 5000000000 92322749733 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042965953/2500000000 : ℝ), (1871168159/2500000000 : ℝ), (-24798763/5000000000 : ℝ)] ![(15812796458907/50000000000000 : ℝ), (17070521080189/25000000000000 : ℝ), (92322749733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042965953/2500000000 : ℝ)|^133 ≤ (15812796458907/50000000000000 : ℝ)^101
        have hw : |(1042965953/2500000000 : ℝ)|=(1042965953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1871168159/2500000000 : ℝ)|^133 ≤ (17070521080189/25000000000000 : ℝ)^101
        have hw : |(1871168159/2500000000 : ℝ)|=(1871168159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24798763/5000000000 : ℝ)|^133 ≤ (92322749733/100000000000000 : ℝ)^101
        have hw : |(-24798763/5000000000 : ℝ)|=(24798763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (515117717/1250000000 : ℝ)*x 0 + (6567255153/10000000000 : ℝ)*x 1 + (961175797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515117717/1250000000 : ℝ)^133 ≤ (3111824954627/10000000000000 : ℝ)^101 := by
    have hnat : (515117717 : ℕ)^133*10000000000000^101 ≤ 3111824954627^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515117717 1250000000 3111824954627 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6567255153/10000000000 : ℝ)^133 ≤ (14370283269641/25000000000000 : ℝ)^101 := by
    have hnat : (6567255153 : ℕ)^133*25000000000000^101 ≤ 14370283269641^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6567255153 10000000000 14370283269641 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961175797/5000000000 : ℝ)^133 ≤ (35626929257/312500000000 : ℝ)^101 := by
    have hnat : (961175797 : ℕ)^133*312500000000^101 ≤ 35626929257^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961175797 5000000000 35626929257 312500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515117717/1250000000 : ℝ), (6567255153/10000000000 : ℝ), (961175797/5000000000 : ℝ)] ![(3111824954627/10000000000000 : ℝ), (14370283269641/25000000000000 : ℝ), (35626929257/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515117717/1250000000 : ℝ)|^133 ≤ (3111824954627/10000000000000 : ℝ)^101
        have hw : |(515117717/1250000000 : ℝ)|=(515117717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6567255153/10000000000 : ℝ)|^133 ≤ (14370283269641/25000000000000 : ℝ)^101
        have hw : |(6567255153/10000000000 : ℝ)|=(6567255153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961175797/5000000000 : ℝ)|^133 ≤ (35626929257/312500000000 : ℝ)^101
        have hw : |(961175797/5000000000 : ℝ)|=(961175797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-138790191/10000000000 : ℝ)*x 0 + (547505113/1250000000 : ℝ)*x 1 + (7287397669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138790191/10000000000 : ℝ)^133 ≤ (357930887189/100000000000000 : ℝ)^101 := by
    have hnat : (138790191 : ℕ)^133*100000000000000^101 ≤ 357930887189^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138790191 10000000000 357930887189 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547505113/1250000000 : ℝ)^133 ≤ (674399261299/2000000000000 : ℝ)^101 := by
    have hnat : (547505113 : ℕ)^133*2000000000000^101 ≤ 674399261299^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547505113 1250000000 674399261299 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7287397669/10000000000 : ℝ)^133 ≤ (6592210604457/10000000000000 : ℝ)^101 := by
    have hnat : (7287397669 : ℕ)^133*10000000000000^101 ≤ 6592210604457^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7287397669 10000000000 6592210604457 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138790191/10000000000 : ℝ), (547505113/1250000000 : ℝ), (7287397669/10000000000 : ℝ)] ![(357930887189/100000000000000 : ℝ), (674399261299/2000000000000 : ℝ), (6592210604457/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138790191/10000000000 : ℝ)|^133 ≤ (357930887189/100000000000000 : ℝ)^101
        have hw : |(-138790191/10000000000 : ℝ)|=(138790191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547505113/1250000000 : ℝ)|^133 ≤ (674399261299/2000000000000 : ℝ)^101
        have hw : |(547505113/1250000000 : ℝ)|=(547505113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7287397669/10000000000 : ℝ)|^133 ≤ (6592210604457/10000000000000 : ℝ)^101
        have hw : |(7287397669/10000000000 : ℝ)|=(7287397669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (100256959/250000000 : ℝ)*x 0 + (-891862361/10000000000 : ℝ)*x 1 + (1455942761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100256959/250000000 : ℝ)^133 ≤ (15011276964499/50000000000000 : ℝ)^101 := by
    have hnat : (100256959 : ℕ)^133*50000000000000^101 ≤ 15011276964499^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100256959 250000000 15011276964499 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891862361/10000000000 : ℝ)^133 ≤ (4146855787379/100000000000000 : ℝ)^101 := by
    have hnat : (891862361 : ℕ)^133*100000000000000^101 ≤ 4146855787379^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891862361 10000000000 4146855787379 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455942761/2000000000 : ℝ)^133 ≤ (65830590266753/100000000000000 : ℝ)^101 := by
    have hnat : (1455942761 : ℕ)^133*100000000000000^101 ≤ 65830590266753^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455942761 2000000000 65830590266753 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100256959/250000000 : ℝ), (-891862361/10000000000 : ℝ), (1455942761/2000000000 : ℝ)] ![(15011276964499/50000000000000 : ℝ), (4146855787379/100000000000000 : ℝ), (65830590266753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100256959/250000000 : ℝ)|^133 ≤ (15011276964499/50000000000000 : ℝ)^101
        have hw : |(100256959/250000000 : ℝ)|=(100256959/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-891862361/10000000000 : ℝ)|^133 ≤ (4146855787379/100000000000000 : ℝ)^101
        have hw : |(-891862361/10000000000 : ℝ)|=(891862361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1455942761/2000000000 : ℝ)|^133 ≤ (65830590266753/100000000000000 : ℝ)^101
        have hw : |(1455942761/2000000000 : ℝ)|=(1455942761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3593994867/5000000000 : ℝ)*x 0 + (451425543/1000000000 : ℝ)*x 1 + (-79672993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3593994867/5000000000 : ℝ)^133 ≤ (32370257112489/50000000000000 : ℝ)^101 := by
    have hnat : (3593994867 : ℕ)^133*50000000000000^101 ≤ 32370257112489^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3593994867 5000000000 32370257112489 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451425543/1000000000 : ℝ)^133 ≤ (17543574091127/50000000000000 : ℝ)^101 := by
    have hnat : (451425543 : ℕ)^133*50000000000000^101 ≤ 17543574091127^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451425543 1000000000 17543574091127 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79672993/10000000000 : ℝ)^133 ≤ (8616879309/5000000000000 : ℝ)^101 := by
    have hnat : (79672993 : ℕ)^133*5000000000000^101 ≤ 8616879309^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79672993 10000000000 8616879309 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3593994867/5000000000 : ℝ), (451425543/1000000000 : ℝ), (-79672993/10000000000 : ℝ)] ![(32370257112489/50000000000000 : ℝ), (17543574091127/50000000000000 : ℝ), (8616879309/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3593994867/5000000000 : ℝ)|^133 ≤ (32370257112489/50000000000000 : ℝ)^101
        have hw : |(3593994867/5000000000 : ℝ)|=(3593994867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451425543/1000000000 : ℝ)|^133 ≤ (17543574091127/50000000000000 : ℝ)^101
        have hw : |(451425543/1000000000 : ℝ)|=(451425543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79672993/10000000000 : ℝ)|^133 ≤ (8616879309/5000000000000 : ℝ)^101
        have hw : |(-79672993/10000000000 : ℝ)|=(79672993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7252311837/10000000000 : ℝ)*x 0 + (659683461/2000000000 : ℝ)*x 1 + (1907496877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7252311837/10000000000 : ℝ)^133 ≤ (818805983823/1250000000000 : ℝ)^101 := by
    have hnat : (7252311837 : ℕ)^133*1250000000000^101 ≤ 818805983823^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7252311837 10000000000 818805983823 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659683461/2000000000 : ℝ)^133 ≤ (11605385127933/50000000000000 : ℝ)^101 := by
    have hnat : (659683461 : ℕ)^133*50000000000000^101 ≤ 11605385127933^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659683461 2000000000 11605385127933 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1907496877/10000000000 : ℝ)^133 ≤ (5642375510181/50000000000000 : ℝ)^101 := by
    have hnat : (1907496877 : ℕ)^133*50000000000000^101 ≤ 5642375510181^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907496877 10000000000 5642375510181 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7252311837/10000000000 : ℝ), (659683461/2000000000 : ℝ), (1907496877/10000000000 : ℝ)] ![(818805983823/1250000000000 : ℝ), (11605385127933/50000000000000 : ℝ), (5642375510181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7252311837/10000000000 : ℝ)|^133 ≤ (818805983823/1250000000000 : ℝ)^101
        have hw : |(7252311837/10000000000 : ℝ)|=(7252311837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659683461/2000000000 : ℝ)|^133 ≤ (11605385127933/50000000000000 : ℝ)^101
        have hw : |(659683461/2000000000 : ℝ)|=(659683461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1907496877/10000000000 : ℝ)|^133 ≤ (5642375510181/50000000000000 : ℝ)^101
        have hw : |(1907496877/10000000000 : ℝ)|=(1907496877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-102083531/10000000000 : ℝ)*x 0 + (1346950393/2000000000 : ℝ)*x 1 + (5018922689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102083531/10000000000 : ℝ)^133 ≤ (119426241827/50000000000000 : ℝ)^101 := by
    have hnat : (102083531 : ℕ)^133*50000000000000^101 ≤ 119426241827^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102083531 10000000000 119426241827 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346950393/2000000000 : ℝ)^133 ≤ (5941942584779/10000000000000 : ℝ)^101 := by
    have hnat : (1346950393 : ℕ)^133*10000000000000^101 ≤ 5941942584779^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346950393 2000000000 5941942584779 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5018922689/10000000000 : ℝ)^133 ≤ (8068344331021/20000000000000 : ℝ)^101 := by
    have hnat : (5018922689 : ℕ)^133*20000000000000^101 ≤ 8068344331021^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5018922689 10000000000 8068344331021 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102083531/10000000000 : ℝ), (1346950393/2000000000 : ℝ), (5018922689/10000000000 : ℝ)] ![(119426241827/50000000000000 : ℝ), (5941942584779/10000000000000 : ℝ), (8068344331021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102083531/10000000000 : ℝ)|^133 ≤ (119426241827/50000000000000 : ℝ)^101
        have hw : |(-102083531/10000000000 : ℝ)|=(102083531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346950393/2000000000 : ℝ)|^133 ≤ (5941942584779/10000000000000 : ℝ)^101
        have hw : |(1346950393/2000000000 : ℝ)|=(1346950393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5018922689/10000000000 : ℝ)|^133 ≤ (8068344331021/20000000000000 : ℝ)^101
        have hw : |(5018922689/10000000000 : ℝ)|=(5018922689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (895449587/1250000000 : ℝ)*x 0 + (-74758349/10000000000 : ℝ)*x 1 + (4543830281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895449587/1250000000 : ℝ)^133 ≤ (64451358938377/100000000000000 : ℝ)^101 := by
    have hnat : (895449587 : ℕ)^133*100000000000000^101 ≤ 64451358938377^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895449587 1250000000 64451358938377 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74758349/10000000000 : ℝ)^133 ≤ (158477541739/100000000000000 : ℝ)^101 := by
    have hnat : (74758349 : ℕ)^133*100000000000000^101 ≤ 158477541739^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74758349 10000000000 158477541739 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543830281/10000000000 : ℝ)^133 ≤ (8847540878599/25000000000000 : ℝ)^101 := by
    have hnat : (4543830281 : ℕ)^133*25000000000000^101 ≤ 8847540878599^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543830281 10000000000 8847540878599 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895449587/1250000000 : ℝ), (-74758349/10000000000 : ℝ), (4543830281/10000000000 : ℝ)] ![(64451358938377/100000000000000 : ℝ), (158477541739/100000000000000 : ℝ), (8847540878599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895449587/1250000000 : ℝ)|^133 ≤ (64451358938377/100000000000000 : ℝ)^101
        have hw : |(895449587/1250000000 : ℝ)|=(895449587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-74758349/10000000000 : ℝ)|^133 ≤ (158477541739/100000000000000 : ℝ)^101
        have hw : |(-74758349/10000000000 : ℝ)|=(74758349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543830281/10000000000 : ℝ)|^133 ≤ (8847540878599/25000000000000 : ℝ)^101
        have hw : |(4543830281/10000000000 : ℝ)|=(4543830281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (996538359/2500000000 : ℝ)*x 0 + (1467293729/2000000000 : ℝ)*x 1 + (-409597737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996538359/2500000000 : ℝ)^133 ≤ (1489247470679/5000000000000 : ℝ)^101 := by
    have hnat : (996538359 : ℕ)^133*5000000000000^101 ≤ 1489247470679^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996538359 2500000000 1489247470679 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1467293729/2000000000 : ℝ)^133 ≤ (16626816933071/25000000000000 : ℝ)^101 := by
    have hnat : (1467293729 : ℕ)^133*25000000000000^101 ≤ 16626816933071^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467293729 2000000000 16626816933071 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409597737/5000000000 : ℝ)^133 ≤ (3707782846047/100000000000000 : ℝ)^101 := by
    have hnat : (409597737 : ℕ)^133*100000000000000^101 ≤ 3707782846047^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409597737 5000000000 3707782846047 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(996538359/2500000000 : ℝ), (1467293729/2000000000 : ℝ), (-409597737/5000000000 : ℝ)] ![(1489247470679/5000000000000 : ℝ), (16626816933071/25000000000000 : ℝ), (3707782846047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(996538359/2500000000 : ℝ)|^133 ≤ (1489247470679/5000000000000 : ℝ)^101
        have hw : |(996538359/2500000000 : ℝ)|=(996538359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1467293729/2000000000 : ℝ)|^133 ≤ (16626816933071/25000000000000 : ℝ)^101
        have hw : |(1467293729/2000000000 : ℝ)|=(1467293729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409597737/5000000000 : ℝ)|^133 ≤ (3707782846047/100000000000000 : ℝ)^101
        have hw : |(-409597737/5000000000 : ℝ)|=(409597737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s5_s5_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7389284323/10000000000 : ℝ)*x 0 + (1363934767/5000000000 : ℝ)*x 1 + (1171038241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7389284323/10000000000 : ℝ)^133 ≤ (6713847118423/10000000000000 : ℝ)^101 := by
    have hnat : (7389284323 : ℕ)^133*10000000000000^101 ≤ 6713847118423^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7389284323 10000000000 6713847118423 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363934767/5000000000 : ℝ)^133 ≤ (9037423621253/50000000000000 : ℝ)^101 := by
    have hnat : (1363934767 : ℕ)^133*50000000000000^101 ≤ 9037423621253^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363934767 5000000000 9037423621253 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171038241/5000000000 : ℝ)^133 ≤ (14786681555879/100000000000000 : ℝ)^101 := by
    have hnat : (1171038241 : ℕ)^133*100000000000000^101 ≤ 14786681555879^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171038241 5000000000 14786681555879 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7389284323/10000000000 : ℝ), (1363934767/5000000000 : ℝ), (1171038241/5000000000 : ℝ)] ![(6713847118423/10000000000000 : ℝ), (9037423621253/50000000000000 : ℝ), (14786681555879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7389284323/10000000000 : ℝ)|^133 ≤ (6713847118423/10000000000000 : ℝ)^101
        have hw : |(7389284323/10000000000 : ℝ)|=(7389284323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363934767/5000000000 : ℝ)|^133 ≤ (9037423621253/50000000000000 : ℝ)^101
        have hw : |(1363934767/5000000000 : ℝ)|=(1363934767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1171038241/5000000000 : ℝ)|^133 ≤ (14786681555879/100000000000000 : ℝ)^101
        have hw : |(1171038241/5000000000 : ℝ)|=(1171038241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304063_s5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((36279/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36279/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18253/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18253/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14053/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14053/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31691/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31691/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4017/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4017/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (36279/50000 : ℝ) ^ (33/8 : ℝ) ≤ (26627284340242894441/100000000000000000000 : ℝ) := by
    have hpowers : (36279/50000 : ℝ)^33 ≤ (26627284340242894441/100000000000000000000 : ℝ)^8 := by
      have hnat : (36279 : ℕ)^33*100000000000000000000^8 ≤ 26627284340242894441^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36279 50000 26627284340242894441 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36279/50000 : ℝ)) (X := (26627284340242894441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0a : (126627284340242894441/100000000000000000000 : ℝ) ≤ (5294501865741717/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (126627284340242894441/100000000000000000000 : ℝ)^8 ≤ (5294501865741717/5000000000000000 : ℝ)^33 := by
      have hnat : (126627284340242894441 : ℕ)^8*5000000000000000^33 ≤ 5294501865741717^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126627284340242894441 100000000000000000000 5294501865741717 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5294501865741717/5000000000000000 : ℝ)) (X := (126627284340242894441/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0b : (76627284340242894441/50000000000000000000 : ℝ) ≤ (2772609576950231/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (76627284340242894441/50000000000000000000 : ℝ)^8 ≤ (2772609576950231/2500000000000000 : ℝ)^33 := by
      have hnat : (76627284340242894441 : ℕ)^8*2500000000000000^33 ≤ 2772609576950231^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76627284340242894441 50000000000000000000 2772609576950231 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2772609576950231/2500000000000000 : ℝ)) (X := (76627284340242894441/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(294501865741717/3627900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(50143457631749/725580000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (36279/50000 : ℝ)) (alpha := (294501865741717/3627900000000000 : ℝ)) (beta := (50143457631749/725580000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36279/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(294501865741717/3627900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(50143457631749/725580000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (18253/25000 : ℝ) ^ (33/8 : ℝ) ≤ (13660646888534956749/50000000000000000000 : ℝ) := by
    have hpowers : (18253/25000 : ℝ)^33 ≤ (13660646888534956749/50000000000000000000 : ℝ)^8 := by
      have hnat : (18253 : ℕ)^33*50000000000000000000^8 ≤ 13660646888534956749^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18253 25000 13660646888534956749 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18253/25000 : ℝ)) (X := (13660646888534956749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1a : (63660646888534956749/50000000000000000000 : ℝ) ≤ (1325380476404251/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (63660646888534956749/50000000000000000000 : ℝ)^8 ≤ (1325380476404251/1250000000000000 : ℝ)^33 := by
      have hnat : (63660646888534956749 : ℕ)^8*1250000000000000^33 ≤ 1325380476404251^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63660646888534956749 50000000000000000000 1325380476404251 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1325380476404251/1250000000000000 : ℝ)) (X := (63660646888534956749/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1b : (38660646888534956749/25000000000000000000 : ℝ) ≤ (2778676410945213/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (38660646888534956749/25000000000000000000 : ℝ)^8 ≤ (2778676410945213/2500000000000000 : ℝ)^33 := by
      have hnat : (38660646888534956749 : ℕ)^8*2500000000000000^33 ≤ 2778676410945213^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38660646888534956749 25000000000000000000 2778676410945213 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2778676410945213/2500000000000000 : ℝ)) (X := (38660646888534956749/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(75380476404251/912650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(127915458136711/1825300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (18253/25000 : ℝ)) (alpha := (75380476404251/912650000000000 : ℝ)) (beta := (127915458136711/1825300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (18253/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(75380476404251/912650000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(127915458136711/1825300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (14053/20000 : ℝ) ^ (33/8 : ℝ) ≤ (4664752212667845703/20000000000000000000 : ℝ) := by
    have hpowers : (14053/20000 : ℝ)^33 ≤ (4664752212667845703/20000000000000000000 : ℝ)^8 := by
      have hnat : (14053 : ℕ)^33*20000000000000000000^8 ≤ 4664752212667845703^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 20000 4664752212667845703 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/20000 : ℝ)) (X := (4664752212667845703/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2a : (24664752212667845703/20000000000000000000 : ℝ) ≤ (2630340371705987/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (24664752212667845703/20000000000000000000 : ℝ)^8 ≤ (2630340371705987/2500000000000000 : ℝ)^33 := by
      have hnat : (24664752212667845703 : ℕ)^8*2500000000000000^33 ≤ 2630340371705987^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24664752212667845703 20000000000000000000 2630340371705987 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2630340371705987/2500000000000000 : ℝ)) (X := (24664752212667845703/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2b : (14664752212667845703/10000000000000000000 : ℝ) ≤ (2743146701189531/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (14664752212667845703/10000000000000000000 : ℝ)^8 ≤ (2743146701189531/2500000000000000 : ℝ)^33 := by
      have hnat : (14664752212667845703 : ℕ)^8*2500000000000000^33 ≤ 2743146701189531^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14664752212667845703 10000000000000000000 2743146701189531 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2743146701189531/2500000000000000 : ℝ)) (X := (14664752212667845703/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5666972682869/76375000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14100791185443/219578125000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (14053/20000 : ℝ)) (alpha := (5666972682869/76375000000000 : ℝ)) (beta := (14100791185443/219578125000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14053/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5666972682869/76375000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14100791185443/219578125000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-254811937/2500000000 : ℝ)*X 0 0+(87623881/156250000 : ℝ)*X 0 1+(2880164237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((5608620681/10000000000 : ℝ)*X 1 0+(-1030182681/10000000000 : ℝ)*X 1 1+(5753313033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((5669276621/10000000000 : ℝ)*X 2 0+(5730452247/10000000000 : ℝ)*X 2 1+(-482489181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((4517928111/10000000000 : ℝ)*X 0 0+(4367985057/10000000000 : ℝ)*X 0 1+(2068471467/5000000000 : ℝ)*X 0 2+(4517928111/10000000000 : ℝ)*X 1 0+(4367985057/10000000000 : ℝ)*X 1 1+(2068471467/5000000000 : ℝ)*X 1 2+(4517928111/10000000000 : ℝ)*X 2 0+(4367985057/10000000000 : ℝ)*X 2 1+(2068471467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-217439477/2500000000 : ℝ)*X 0 0+(163545767/400000000 : ℝ)*X 0 1+(289035799/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4449352151/10000000000 : ℝ)*X 1 0+(-86074223/5000000000 : ℝ)*X 1 1+(7218305479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((1042965953/2500000000 : ℝ)*X 2 0+(1871168159/2500000000 : ℝ)*X 2 1+(-24798763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((515117717/1250000000 : ℝ)*X 0 0+(6567255153/10000000000 : ℝ)*X 0 1+(961175797/5000000000 : ℝ)*X 0 2+(515117717/1250000000 : ℝ)*X 1 0+(6567255153/10000000000 : ℝ)*X 1 1+(961175797/5000000000 : ℝ)*X 1 2+(515117717/1250000000 : ℝ)*X 2 0+(6567255153/10000000000 : ℝ)*X 2 1+(961175797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-138790191/10000000000 : ℝ)*X 0 0+(547505113/1250000000 : ℝ)*X 0 1+(7287397669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((100256959/250000000 : ℝ)*X 1 0+(-891862361/10000000000 : ℝ)*X 1 1+(1455942761/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((3593994867/5000000000 : ℝ)*X 2 0+(451425543/1000000000 : ℝ)*X 2 1+(-79672993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((7252311837/10000000000 : ℝ)*X 0 0+(659683461/2000000000 : ℝ)*X 0 1+(1907496877/10000000000 : ℝ)*X 0 2+(7252311837/10000000000 : ℝ)*X 1 0+(659683461/2000000000 : ℝ)*X 1 1+(1907496877/10000000000 : ℝ)*X 1 2+(7252311837/10000000000 : ℝ)*X 2 0+(659683461/2000000000 : ℝ)*X 2 1+(1907496877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-102083531/10000000000 : ℝ)*X 0 0+(1346950393/2000000000 : ℝ)*X 0 1+(5018922689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((895449587/1250000000 : ℝ)*X 1 0+(-74758349/10000000000 : ℝ)*X 1 1+(4543830281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((996538359/2500000000 : ℝ)*X 2 0+(1467293729/2000000000 : ℝ)*X 2 1+(-409597737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((7389284323/10000000000 : ℝ)*X 0 0+(1363934767/5000000000 : ℝ)*X 0 1+(1171038241/5000000000 : ℝ)*X 0 2+(7389284323/10000000000 : ℝ)*X 1 0+(1363934767/5000000000 : ℝ)*X 1 1+(1171038241/5000000000 : ℝ)*X 1 2+(7389284323/10000000000 : ℝ)*X 2 0+(1363934767/5000000000 : ℝ)*X 2 1+(1171038241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((31691/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31691/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28783852551799874939847717/2788145750000000000000000000000 : ℝ) := by norm_num
    linear_combination (261571076361/1000000000000 : ℝ)*(base7) + (531673/500000000000 : ℝ)*(base50) + (117488988061/1000000000000 : ℝ)*(base60) + (2676249585547/1000000000000 : ℝ)*(major_s5_0) + (2676249585547/1000000000000 : ℝ)*(major_s5_1) + (2676249585547/1000000000000 : ℝ)*(major_s5_2) + (2202889/200000000000 : ℝ)*(sp_s5_0) + (1682577/1000000000000 : ℝ)*(sp_s5_6) + (684829593837/200000000000 : ℝ)*(sp_s5_7) + (1712117752429/500000000000 : ℝ)*(sp_s5_8) + (3424235808083/1000000000000 : ℝ)*(sp_s5_9) + (2026067511793/1000000000000 : ℝ)*(sp_s5_13) + (19206113/250000000000 : ℝ)*(sp_s5_14) + (12129/40000000000 : ℝ)*(sp_s5_15) + (1764498118009/1000000000000 : ℝ)*(f.failure) + (3424235808083/1000000000000 : ℝ)*(f.sum) + (134345726140290323/174259109375000000000000000000 : ℝ)*base63 + (985140766769811/3513250000000000000000000000 : ℝ)*base65 + (582539232133827/1825300000000000000000000000 : ℝ)*base67 + (91133634299111/152750000000000000000000000 : ℝ)*base69 + (95606945879642412127/254914393500000000000000000000000 : ℝ)*base70 + (37464258444317/725580000000000000000000000 : ℝ)*base73 + (261663144150091/456325000000000000000000000 : ℝ)*base75 + (742153934467459/3627900000000000000000000000 : ℝ)*base77 + (16101371152535182801/33110029350000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (4869/12500000000000000 : ℝ)*base86 + (4869/12500000000000000 : ℝ)*base88 + (4869/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4017/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4017/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6583138072220606571216186024947/775492070759250000000000000000000000 : ℝ) := by norm_num
    linear_combination (31323636017/100000000000 : ℝ)*(base7) + (869/1600000000 : ℝ)*(base49) + (28773/125000000000 : ℝ)*(base59) + (2543663932169/1000000000000 : ℝ)*(major_s5_0) + (2543663932169/1000000000000 : ℝ)*(major_s5_1) + (2543663932169/1000000000000 : ℝ)*(major_s5_2) + (665249/200000000000 : ℝ)*(sp_s5_1) + (286487/200000000000 : ℝ)*(sp_s5_2) + (27199383/500000000000 : ℝ)*(sp_s5_8) + (3214135066799/1000000000000 : ℝ)*(sp_s5_14) + (803519335447/250000000000 : ℝ)*(sp_s5_15) + (803533408591/250000000000 : ℝ)*(sp_s5_16) + (1990281592629/1000000000000 : ℝ)*(sp_s5_20) + (36847403/1000000000000 : ℝ)*(sp_s5_27) + (838541039931/500000000000 : ℝ)*(f.failure) + (3214135066799/1000000000000 : ℝ)*(f.sum) + (1074373923338977/87129554687500000000000000000 : ℝ)*base62 + (1709882392874397/3513250000000000000000000000 : ℝ)*base65 + (135845239808859/1825300000000000000000000000 : ℝ)*base67 + (9335865451647/152750000000000000000000000 : ℝ)*base69 + (114887336630688504121/254914393500000000000000000000000 : ℝ)*base71 + (30281317886063/725580000000000000000000000 : ℝ)*base72 + (2075259264937/456325000000000000000000000 : ℝ)*base75 + (139378164770693/3627900000000000000000000000 : ℝ)*base77 + (64581043007090699/1034688417187500000000000000000 : ℝ)*base79 + (4421/6250000000000000 : ℝ)*base86 + (4421/6250000000000000 : ℝ)*base88 + (4421/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (105068991487395041165038825471/11239015518250000000000000000000000 : ℝ) := by norm_num
    linear_combination (304269323963/1000000000000 : ℝ)*(base7) + (144083408521/1000000000000 : ℝ)*(base40) + (1249529/1000000000000 : ℝ)*(base49) + (2441437522141/1000000000000 : ℝ)*(major_s5_0) + (2441437522141/1000000000000 : ℝ)*(major_s5_1) + (2441437522141/1000000000000 : ℝ)*(major_s5_2) + (4710847/500000000000 : ℝ)*(sp_s5_1) + (23233907/1000000000000 : ℝ)*(sp_s5_2) + (86388631/1000000000000 : ℝ)*(sp_s5_9) + (14101171/1000000000000 : ℝ)*(sp_s5_20) + (1541347805527/500000000000 : ℝ)*(sp_s5_21) + (38533577367/12500000000 : ℝ)*(sp_s5_22) + (770646497129/250000000000 : ℝ)*(sp_s5_23) + (956968822081/500000000000 : ℝ)*(sp_s5_27) + (160968242137/100000000000 : ℝ)*(f.failure) + (1541347805527/500000000000 : ℝ)*(f.sum) + (657407408280722127/1394072875000000000000000000000 : ℝ)*base63 + (181425173403817/3513250000000000000000000000 : ℝ)*base64 + (365133983658041/1825300000000000000000000000 : ℝ)*base67 + (40302839452633/152750000000000000000000000 : ℝ)*base69 + (185555465820588575219/254914393500000000000000000000000 : ℝ)*base71 + (81127655401289/145116000000000000000000000 : ℝ)*base72 + (241204665880671/912650000000000000000000000 : ℝ)*base75 + (1671705887915977/3627900000000000000000000000 : ℝ)*base77 + (1050938522301376019/16555014675000000000000000000000 : ℝ)*base78 + (867/1250000000000000 : ℝ)*base86 + (867/1250000000000000 : ℝ)*base88 + (867/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((36279/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36279/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18253/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18253/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14053/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14053/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31691/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31691/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4017/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4017/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61709/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61709/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304063_s5 p hpa hpb X hX hprev4

#print axioms solution
