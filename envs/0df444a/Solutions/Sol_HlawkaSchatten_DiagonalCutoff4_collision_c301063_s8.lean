-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063_s8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:41:01.712051+00:00
-- url     : https://prove2.me/submissions/f0af4848-3197-426d-a15d-a239e9c39975

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
theorem collision_support_c301063_s8_s8_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994101433/10000000000 : ℝ)*x 0 + (5385511667/10000000000 : ℝ)*x 1 + (5405709907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994101433/10000000000 : ℝ)^65 ≤ (11778589464029/100000000000000 : ℝ)^49 := by
    have hnat : (1994101433 : ℕ)^65*100000000000000^49 ≤ 11778589464029^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994101433 10000000000 11778589464029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385511667/10000000000 : ℝ)^65 ≤ (44001182640211/100000000000000 : ℝ)^49 := by
    have hnat : (5385511667 : ℕ)^65*100000000000000^49 ≤ 44001182640211^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385511667 10000000000 44001182640211 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405709907/10000000000 : ℝ)^65 ≤ (44220227873521/100000000000000 : ℝ)^49 := by
    have hnat : (5405709907 : ℕ)^65*100000000000000^49 ≤ 44220227873521^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405709907 10000000000 44220227873521 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994101433/10000000000 : ℝ), (5385511667/10000000000 : ℝ), (5405709907/10000000000 : ℝ)] ![(11778589464029/100000000000000 : ℝ), (44001182640211/100000000000000 : ℝ), (44220227873521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994101433/10000000000 : ℝ)|^65 ≤ (11778589464029/100000000000000 : ℝ)^49
        have hw : |(-1994101433/10000000000 : ℝ)|=(1994101433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385511667/10000000000 : ℝ)|^65 ≤ (44001182640211/100000000000000 : ℝ)^49
        have hw : |(5385511667/10000000000 : ℝ)|=(5385511667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405709907/10000000000 : ℝ)|^65 ≤ (44220227873521/100000000000000 : ℝ)^49
        have hw : |(5405709907/10000000000 : ℝ)|=(5405709907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1346530939/2500000000 : ℝ)*x 0 + (-499806033/2500000000 : ℝ)*x 1 + (5401397509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346530939/2500000000 : ℝ)^65 ≤ (44007816668027/100000000000000 : ℝ)^49 := by
    have hnat : (1346530939 : ℕ)^65*100000000000000^49 ≤ 44007816668027^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346530939 2500000000 44007816668027 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499806033/2500000000 : ℝ)^65 ≤ (738671555187/6250000000000 : ℝ)^49 := by
    have hnat : (499806033 : ℕ)^65*6250000000000^49 ≤ 738671555187^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499806033 2500000000 738671555187 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401397509/10000000000 : ℝ)^65 ≤ (44173438441371/100000000000000 : ℝ)^49 := by
    have hnat : (5401397509 : ℕ)^65*100000000000000^49 ≤ 44173438441371^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401397509 10000000000 44173438441371 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346530939/2500000000 : ℝ), (-499806033/2500000000 : ℝ), (5401397509/10000000000 : ℝ)] ![(44007816668027/100000000000000 : ℝ), (738671555187/6250000000000 : ℝ), (44173438441371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346530939/2500000000 : ℝ)|^65 ≤ (44007816668027/100000000000000 : ℝ)^49
        have hw : |(1346530939/2500000000 : ℝ)|=(1346530939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499806033/2500000000 : ℝ)|^65 ≤ (738671555187/6250000000000 : ℝ)^49
        have hw : |(-499806033/2500000000 : ℝ)|=(499806033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401397509/10000000000 : ℝ)|^65 ≤ (44173438441371/100000000000000 : ℝ)^49
        have hw : |(5401397509/10000000000 : ℝ)|=(5401397509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5402007987/10000000000 : ℝ)*x 0 + (539859573/1000000000 : ℝ)*x 1 + (-1981108537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402007987/10000000000 : ℝ)^65 ≤ (276125383591/625000000000 : ℝ)^49 := by
    have hnat : (5402007987 : ℕ)^65*625000000000^49 ≤ 276125383591^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402007987 10000000000 276125383591 625000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539859573/1000000000 : ℝ)^65 ≤ (22071522865441/50000000000000 : ℝ)^49 := by
    have hnat : (539859573 : ℕ)^65*50000000000000^49 ≤ 22071522865441^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539859573 1000000000 22071522865441 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981108537/10000000000 : ℝ)^65 ≤ (11676892881397/100000000000000 : ℝ)^49 := by
    have hnat : (1981108537 : ℕ)^65*100000000000000^49 ≤ 11676892881397^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981108537 10000000000 11676892881397 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402007987/10000000000 : ℝ), (539859573/1000000000 : ℝ), (-1981108537/10000000000 : ℝ)] ![(276125383591/625000000000 : ℝ), (22071522865441/50000000000000 : ℝ), (11676892881397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402007987/10000000000 : ℝ)|^65 ≤ (276125383591/625000000000 : ℝ)^49
        have hw : |(5402007987/10000000000 : ℝ)|=(5402007987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539859573/1000000000 : ℝ)|^65 ≤ (22071522865441/50000000000000 : ℝ)^49
        have hw : |(539859573/1000000000 : ℝ)|=(539859573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981108537/10000000000 : ℝ)|^65 ≤ (11676892881397/100000000000000 : ℝ)^49
        have hw : |(-1981108537/10000000000 : ℝ)|=(1981108537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4373068641/10000000000 : ℝ)*x 0 + (34147683/78125000 : ℝ)*x 1 + (4361272627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373068641/10000000000 : ℝ)^65 ≤ (33380437383663/100000000000000 : ℝ)^49 := by
    have hnat : (4373068641 : ℕ)^65*100000000000000^49 ≤ 33380437383663^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373068641 10000000000 33380437383663 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34147683/78125000 : ℝ)^65 ≤ (16679257460949/50000000000000 : ℝ)^49 := by
    have hnat : (34147683 : ℕ)^65*50000000000000^49 ≤ 16679257460949^49*78125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34147683 78125000 16679257460949 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4361272627/10000000000 : ℝ)^65 ≤ (33261047682489/100000000000000 : ℝ)^49 := by
    have hnat : (4361272627 : ℕ)^65*100000000000000^49 ≤ 33261047682489^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361272627 10000000000 33261047682489 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373068641/10000000000 : ℝ), (34147683/78125000 : ℝ), (4361272627/10000000000 : ℝ)] ![(33380437383663/100000000000000 : ℝ), (16679257460949/50000000000000 : ℝ), (33261047682489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373068641/10000000000 : ℝ)|^65 ≤ (33380437383663/100000000000000 : ℝ)^49
        have hw : |(4373068641/10000000000 : ℝ)|=(4373068641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34147683/78125000 : ℝ)|^65 ≤ (16679257460949/50000000000000 : ℝ)^49
        have hw : |(34147683/78125000 : ℝ)|=(34147683/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4361272627/10000000000 : ℝ)|^65 ≤ (33261047682489/100000000000000 : ℝ)^49
        have hw : |(4361272627/10000000000 : ℝ)|=(4361272627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-379560193/2000000000 : ℝ)*x 0 + (4651160957/10000000000 : ℝ)*x 1 + (123479913/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379560193/2000000000 : ℝ)^65 ≤ (1378756025051/12500000000000 : ℝ)^49 := by
    have hnat : (379560193 : ℕ)^65*12500000000000^49 ≤ 1378756025051^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379560193 2000000000 1378756025051 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4651160957/10000000000 : ℝ)^65 ≤ (36225132203959/100000000000000 : ℝ)^49 := by
    have hnat : (4651160957 : ℕ)^65*100000000000000^49 ≤ 36225132203959^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4651160957 10000000000 36225132203959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123479913/200000000 : ℝ)^65 ≤ (26372409790887/50000000000000 : ℝ)^49 := by
    have hnat : (123479913 : ℕ)^65*50000000000000^49 ≤ 26372409790887^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123479913 200000000 26372409790887 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379560193/2000000000 : ℝ), (4651160957/10000000000 : ℝ), (123479913/200000000 : ℝ)] ![(1378756025051/12500000000000 : ℝ), (36225132203959/100000000000000 : ℝ), (26372409790887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379560193/2000000000 : ℝ)|^65 ≤ (1378756025051/12500000000000 : ℝ)^49
        have hw : |(-379560193/2000000000 : ℝ)|=(379560193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4651160957/10000000000 : ℝ)|^65 ≤ (36225132203959/100000000000000 : ℝ)^49
        have hw : |(4651160957/10000000000 : ℝ)|=(4651160957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123479913/200000000 : ℝ)|^65 ≤ (26372409790887/50000000000000 : ℝ)^49
        have hw : |(123479913/200000000 : ℝ)|=(123479913/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (126902793/250000000 : ℝ)*x 0 + (-646117273/5000000000 : ℝ)*x 1 + (1233929591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126902793/250000000 : ℝ)^65 ≤ (40679732193873/100000000000000 : ℝ)^49 := by
    have hnat : (126902793 : ℕ)^65*100000000000000^49 ≤ 40679732193873^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126902793 250000000 40679732193873 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646117273/5000000000 : ℝ)^65 ≤ (6624713378877/100000000000000 : ℝ)^49 := by
    have hnat : (646117273 : ℕ)^65*100000000000000^49 ≤ 6624713378877^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646117273 5000000000 6624713378877 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233929591/2000000000 : ℝ)^65 ≤ (26347777210947/50000000000000 : ℝ)^49 := by
    have hnat : (1233929591 : ℕ)^65*50000000000000^49 ≤ 26347777210947^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233929591 2000000000 26347777210947 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126902793/250000000 : ℝ), (-646117273/5000000000 : ℝ), (1233929591/2000000000 : ℝ)] ![(40679732193873/100000000000000 : ℝ), (6624713378877/100000000000000 : ℝ), (26347777210947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126902793/250000000 : ℝ)|^65 ≤ (40679732193873/100000000000000 : ℝ)^49
        have hw : |(126902793/250000000 : ℝ)|=(126902793/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-646117273/5000000000 : ℝ)|^65 ≤ (6624713378877/100000000000000 : ℝ)^49
        have hw : |(-646117273/5000000000 : ℝ)|=(646117273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1233929591/2000000000 : ℝ)|^65 ≤ (26347777210947/50000000000000 : ℝ)^49
        have hw : |(1233929591/2000000000 : ℝ)|=(1233929591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4913780557/10000000000 : ℝ)*x 0 + (6336513033/10000000000 : ℝ)*x 1 + (-316335617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4913780557/10000000000 : ℝ)^65 ≤ (38963104739/100000000000 : ℝ)^49 := by
    have hnat : (4913780557 : ℕ)^65*100000000000^49 ≤ 38963104739^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913780557 10000000000 38963104739 100000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6336513033/10000000000 : ℝ)^65 ≤ (3412152379149/6250000000000 : ℝ)^49 := by
    have hnat : (6336513033 : ℕ)^65*6250000000000^49 ≤ 3412152379149^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6336513033 10000000000 3412152379149 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316335617/2500000000 : ℝ)^65 ≤ (1610614293823/25000000000000 : ℝ)^49 := by
    have hnat : (316335617 : ℕ)^65*25000000000000^49 ≤ 1610614293823^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316335617 2500000000 1610614293823 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4913780557/10000000000 : ℝ), (6336513033/10000000000 : ℝ), (-316335617/2500000000 : ℝ)] ![(38963104739/100000000000 : ℝ), (3412152379149/6250000000000 : ℝ), (1610614293823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4913780557/10000000000 : ℝ)|^65 ≤ (38963104739/100000000000 : ℝ)^49
        have hw : |(4913780557/10000000000 : ℝ)|=(4913780557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6336513033/10000000000 : ℝ)|^65 ≤ (3412152379149/6250000000000 : ℝ)^49
        have hw : |(6336513033/10000000000 : ℝ)|=(6336513033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-316335617/2500000000 : ℝ)|^65 ≤ (1610614293823/25000000000000 : ℝ)^49
        have hw : |(-316335617/2500000000 : ℝ)|=(316335617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4505951927/10000000000 : ℝ)*x 0 + (2767422561/5000000000 : ℝ)*x 1 + (2931870467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505951927/10000000000 : ℝ)^65 ≤ (34732597661261/100000000000000 : ℝ)^49 := by
    have hnat : (4505951927 : ℕ)^65*100000000000000^49 ≤ 34732597661261^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505951927 10000000000 34732597661261 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767422561/5000000000 : ℝ)^65 ≤ (45626961226629/100000000000000 : ℝ)^49 := by
    have hnat : (2767422561 : ℕ)^65*100000000000000^49 ≤ 45626961226629^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767422561 5000000000 45626961226629 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2931870467/10000000000 : ℝ)^65 ≤ (19640441097209/100000000000000 : ℝ)^49 := by
    have hnat : (2931870467 : ℕ)^65*100000000000000^49 ≤ 19640441097209^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2931870467 10000000000 19640441097209 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505951927/10000000000 : ℝ), (2767422561/5000000000 : ℝ), (2931870467/10000000000 : ℝ)] ![(34732597661261/100000000000000 : ℝ), (45626961226629/100000000000000 : ℝ), (19640441097209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505951927/10000000000 : ℝ)|^65 ≤ (34732597661261/100000000000000 : ℝ)^49
        have hw : |(4505951927/10000000000 : ℝ)|=(4505951927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767422561/5000000000 : ℝ)|^65 ≤ (45626961226629/100000000000000 : ℝ)^49
        have hw : |(2767422561/5000000000 : ℝ)|=(2767422561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2931870467/10000000000 : ℝ)|^65 ≤ (19640441097209/100000000000000 : ℝ)^49
        have hw : |(2931870467/10000000000 : ℝ)|=(2931870467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1287334881/10000000000 : ℝ)*x 0 + (5083554319/10000000000 : ℝ)*x 1 + (6165601661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1287334881/10000000000 : ℝ)^65 ≤ (1647853421047/25000000000000 : ℝ)^49 := by
    have hnat : (1287334881 : ℕ)^65*25000000000000^49 ≤ 1647853421047^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287334881 10000000000 1647853421047 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083554319/10000000000 : ℝ)^65 ≤ (20379435794339/50000000000000 : ℝ)^49 := by
    have hnat : (5083554319 : ℕ)^65*50000000000000^49 ≤ 20379435794339^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083554319 10000000000 20379435794339 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6165601661/10000000000 : ℝ)^65 ≤ (52649714718957/100000000000000 : ℝ)^49 := by
    have hnat : (6165601661 : ℕ)^65*100000000000000^49 ≤ 52649714718957^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6165601661 10000000000 52649714718957 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1287334881/10000000000 : ℝ), (5083554319/10000000000 : ℝ), (6165601661/10000000000 : ℝ)] ![(1647853421047/25000000000000 : ℝ), (20379435794339/50000000000000 : ℝ), (52649714718957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1287334881/10000000000 : ℝ)|^65 ≤ (1647853421047/25000000000000 : ℝ)^49
        have hw : |(-1287334881/10000000000 : ℝ)|=(1287334881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083554319/10000000000 : ℝ)|^65 ≤ (20379435794339/50000000000000 : ℝ)^49
        have hw : |(5083554319/10000000000 : ℝ)|=(5083554319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6165601661/10000000000 : ℝ)|^65 ≤ (52649714718957/100000000000000 : ℝ)^49
        have hw : |(6165601661/10000000000 : ℝ)|=(6165601661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4666992219/10000000000 : ℝ)*x 0 + (-1895293231/10000000000 : ℝ)*x 1 + (3080628117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4666992219/10000000000 : ℝ)^65 ≤ (18194392327433/50000000000000 : ℝ)^49 := by
    have hnat : (4666992219 : ℕ)^65*50000000000000^49 ≤ 18194392327433^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4666992219 10000000000 18194392327433 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895293231/10000000000 : ℝ)^65 ≤ (5505359102283/50000000000000 : ℝ)^49 := by
    have hnat : (1895293231 : ℕ)^65*50000000000000^49 ≤ 5505359102283^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895293231 10000000000 5505359102283 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3080628117/5000000000 : ℝ)^65 ≤ (52600497132747/100000000000000 : ℝ)^49 := by
    have hnat : (3080628117 : ℕ)^65*100000000000000^49 ≤ 52600497132747^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080628117 5000000000 52600497132747 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4666992219/10000000000 : ℝ), (-1895293231/10000000000 : ℝ), (3080628117/5000000000 : ℝ)] ![(18194392327433/50000000000000 : ℝ), (5505359102283/50000000000000 : ℝ), (52600497132747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4666992219/10000000000 : ℝ)|^65 ≤ (18194392327433/50000000000000 : ℝ)^49
        have hw : |(4666992219/10000000000 : ℝ)|=(4666992219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895293231/10000000000 : ℝ)|^65 ≤ (5505359102283/50000000000000 : ℝ)^49
        have hw : |(-1895293231/10000000000 : ℝ)|=(1895293231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3080628117/5000000000 : ℝ)|^65 ≤ (52600497132747/100000000000000 : ℝ)^49
        have hw : |(3080628117/5000000000 : ℝ)|=(3080628117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6161395611/10000000000 : ℝ)*x 0 + (5096697727/10000000000 : ℝ)*x 1 + (-1273735151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6161395611/10000000000 : ℝ)^65 ≤ (3287629723863/6250000000000 : ℝ)^49 := by
    have hnat : (6161395611 : ℕ)^65*6250000000000^49 ≤ 3287629723863^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6161395611 10000000000 3287629723863 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5096697727/10000000000 : ℝ)^65 ≤ (20449360900261/50000000000000 : ℝ)^49 := by
    have hnat : (5096697727 : ℕ)^65*50000000000000^49 ≤ 20449360900261^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096697727 10000000000 20449360900261 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1273735151/10000000000 : ℝ)^65 ≤ (406200162869/6250000000000 : ℝ)^49 := by
    have hnat : (1273735151 : ℕ)^65*6250000000000^49 ≤ 406200162869^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273735151 10000000000 406200162869 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6161395611/10000000000 : ℝ), (5096697727/10000000000 : ℝ), (-1273735151/10000000000 : ℝ)] ![(3287629723863/6250000000000 : ℝ), (20449360900261/50000000000000 : ℝ), (406200162869/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6161395611/10000000000 : ℝ)|^65 ≤ (3287629723863/6250000000000 : ℝ)^49
        have hw : |(6161395611/10000000000 : ℝ)|=(6161395611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5096697727/10000000000 : ℝ)|^65 ≤ (20449360900261/50000000000000 : ℝ)^49
        have hw : |(5096697727/10000000000 : ℝ)|=(5096697727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1273735151/10000000000 : ℝ)|^65 ≤ (406200162869/6250000000000 : ℝ)^49
        have hw : |(-1273735151/10000000000 : ℝ)|=(1273735151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5856398927/10000000000 : ℝ)*x 0 + (4139587811/10000000000 : ℝ)*x 1 + (147415431/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5856398927/10000000000 : ℝ)^65 ≤ (1536756181539/3125000000000 : ℝ)^49 := by
    have hnat : (5856398927 : ℕ)^65*3125000000000^49 ≤ 1536756181539^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5856398927 10000000000 1536756181539 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139587811/10000000000 : ℝ)^65 ≤ (31037152254463/100000000000000 : ℝ)^49 := by
    have hnat : (4139587811 : ℕ)^65*100000000000000^49 ≤ 31037152254463^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139587811 10000000000 31037152254463 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147415431/500000000 : ℝ)^65 ≤ (2473331241581/12500000000000 : ℝ)^49 := by
    have hnat : (147415431 : ℕ)^65*12500000000000^49 ≤ 2473331241581^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147415431 500000000 2473331241581 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5856398927/10000000000 : ℝ), (4139587811/10000000000 : ℝ), (147415431/500000000 : ℝ)] ![(1536756181539/3125000000000 : ℝ), (31037152254463/100000000000000 : ℝ), (2473331241581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5856398927/10000000000 : ℝ)|^65 ≤ (1536756181539/3125000000000 : ℝ)^49
        have hw : |(5856398927/10000000000 : ℝ)|=(5856398927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139587811/10000000000 : ℝ)|^65 ≤ (31037152254463/100000000000000 : ℝ)^49
        have hw : |(4139587811/10000000000 : ℝ)|=(4139587811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147415431/500000000 : ℝ)|^65 ≤ (2473331241581/12500000000000 : ℝ)^49
        have hw : |(147415431/500000000 : ℝ)|=(147415431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-617292661/5000000000 : ℝ)*x 0 + (1167060389/2000000000 : ℝ)*x 1 + (546117507/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (617292661/5000000000 : ℝ)^65 ≤ (1247110502423/20000000000000 : ℝ)^49 := by
    have hnat : (617292661 : ℕ)^65*20000000000000^49 ≤ 1247110502423^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617292661 5000000000 1247110502423 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167060389/2000000000 : ℝ)^65 ≤ (48941339357361/100000000000000 : ℝ)^49 := by
    have hnat : (1167060389 : ℕ)^65*100000000000000^49 ≤ 48941339357361^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167060389 2000000000 48941339357361 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546117507/1000000000 : ℝ)^65 ≤ (4482310812433/10000000000000 : ℝ)^49 := by
    have hnat : (546117507 : ℕ)^65*10000000000000^49 ≤ 4482310812433^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546117507 1000000000 4482310812433 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-617292661/5000000000 : ℝ), (1167060389/2000000000 : ℝ), (546117507/1000000000 : ℝ)] ![(1247110502423/20000000000000 : ℝ), (48941339357361/100000000000000 : ℝ), (4482310812433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-617292661/5000000000 : ℝ)|^65 ≤ (1247110502423/20000000000000 : ℝ)^49
        have hw : |(-617292661/5000000000 : ℝ)|=(617292661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167060389/2000000000 : ℝ)|^65 ≤ (48941339357361/100000000000000 : ℝ)^49
        have hw : |(1167060389/2000000000 : ℝ)|=(1167060389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546117507/1000000000 : ℝ)|^65 ≤ (4482310812433/10000000000000 : ℝ)^49
        have hw : |(546117507/1000000000 : ℝ)|=(546117507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1239622011/2000000000 : ℝ)*x 0 + (-1230217201/10000000000 : ℝ)*x 1 + (2542555233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239622011/2000000000 : ℝ)^65 ≤ (53018273361341/100000000000000 : ℝ)^49 := by
    have hnat : (1239622011 : ℕ)^65*100000000000000^49 ≤ 53018273361341^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239622011 2000000000 53018273361341 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230217201/10000000000 : ℝ)^65 ≤ (6206303269529/100000000000000 : ℝ)^49 := by
    have hnat : (1230217201 : ℕ)^65*100000000000000^49 ≤ 6206303269529^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230217201 10000000000 6206303269529 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542555233/5000000000 : ℝ)^65 ≤ (40775423352589/100000000000000 : ℝ)^49 := by
    have hnat : (2542555233 : ℕ)^65*100000000000000^49 ≤ 40775423352589^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542555233 5000000000 40775423352589 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1239622011/2000000000 : ℝ), (-1230217201/10000000000 : ℝ), (2542555233/5000000000 : ℝ)] ![(53018273361341/100000000000000 : ℝ), (6206303269529/100000000000000 : ℝ), (40775423352589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1239622011/2000000000 : ℝ)|^65 ≤ (53018273361341/100000000000000 : ℝ)^49
        have hw : |(1239622011/2000000000 : ℝ)|=(1239622011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1230217201/10000000000 : ℝ)|^65 ≤ (6206303269529/100000000000000 : ℝ)^49
        have hw : |(-1230217201/10000000000 : ℝ)|=(1230217201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542555233/5000000000 : ℝ)|^65 ≤ (40775423352589/100000000000000 : ℝ)^49
        have hw : |(2542555233/5000000000 : ℝ)|=(2542555233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (36065867/78125000 : ℝ)*x 0 + (6220165071/10000000000 : ℝ)*x 1 + (-1876297269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36065867/78125000 : ℝ)^65 ≤ (17933377749303/50000000000000 : ℝ)^49 := by
    have hnat : (36065867 : ℕ)^65*50000000000000^49 ≤ 17933377749303^49*78125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36065867 78125000 17933377749303 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6220165071/10000000000 : ℝ)^65 ≤ (53268678352589/100000000000000 : ℝ)^49 := by
    have hnat : (6220165071 : ℕ)^65*100000000000000^49 ≤ 53268678352589^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6220165071 10000000000 53268678352589 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876297269/10000000000 : ℝ)^65 ≤ (10864566140649/100000000000000 : ℝ)^49 := by
    have hnat : (1876297269 : ℕ)^65*100000000000000^49 ≤ 10864566140649^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876297269 10000000000 10864566140649 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36065867/78125000 : ℝ), (6220165071/10000000000 : ℝ), (-1876297269/10000000000 : ℝ)] ![(17933377749303/50000000000000 : ℝ), (53268678352589/100000000000000 : ℝ), (10864566140649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36065867/78125000 : ℝ)|^65 ≤ (17933377749303/50000000000000 : ℝ)^49
        have hw : |(36065867/78125000 : ℝ)|=(36065867/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6220165071/10000000000 : ℝ)|^65 ≤ (53268678352589/100000000000000 : ℝ)^49
        have hw : |(6220165071/10000000000 : ℝ)|=(6220165071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876297269/10000000000 : ℝ)|^65 ≤ (10864566140649/100000000000000 : ℝ)^49
        have hw : |(-1876297269/10000000000 : ℝ)|=(1876297269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s8_s8_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1496706589/2500000000 : ℝ)*x 0 + (1782527181/5000000000 : ℝ)*x 1 + (1700205341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1496706589/2500000000 : ℝ)^65 ≤ (50634269814827/100000000000000 : ℝ)^49 := by
    have hnat : (1496706589 : ℕ)^65*100000000000000^49 ≤ 50634269814827^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496706589 2500000000 50634269814827 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782527181/5000000000 : ℝ)^65 ≤ (6364174119719/25000000000000 : ℝ)^49 := by
    have hnat : (1782527181 : ℕ)^65*25000000000000^49 ≤ 6364174119719^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782527181 5000000000 6364174119719 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1700205341/5000000000 : ℝ)^65 ≤ (23909033680577/100000000000000 : ℝ)^49 := by
    have hnat : (1700205341 : ℕ)^65*100000000000000^49 ≤ 23909033680577^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700205341 5000000000 23909033680577 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1496706589/2500000000 : ℝ), (1782527181/5000000000 : ℝ), (1700205341/5000000000 : ℝ)] ![(50634269814827/100000000000000 : ℝ), (6364174119719/25000000000000 : ℝ), (23909033680577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1496706589/2500000000 : ℝ)|^65 ≤ (50634269814827/100000000000000 : ℝ)^49
        have hw : |(1496706589/2500000000 : ℝ)|=(1496706589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1782527181/5000000000 : ℝ)|^65 ≤ (6364174119719/25000000000000 : ℝ)^49
        have hw : |(1782527181/5000000000 : ℝ)|=(1782527181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1700205341/5000000000 : ℝ)|^65 ≤ (23909033680577/100000000000000 : ℝ)^49
        have hw : |(1700205341/5000000000 : ℝ)|=(1700205341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301063_s8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((10009/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10009/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38663/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3839/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3839/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31007/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14821/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14821/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev7 with ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩
  have s8_pow0 : (10009/25000 : ℝ) ^ (129/32 : ℝ) ≤ (78024200596511903/3125000000000000000 : ℝ) := by
    have hpowers : (10009/25000 : ℝ)^129 ≤ (78024200596511903/3125000000000000000 : ℝ)^32 := by
      have hnat : (10009 : ℕ)^129*3125000000000000000^32 ≤ 78024200596511903^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009 25000 78024200596511903 3125000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10009/25000 : ℝ)) (X := (78024200596511903/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s8_corner0a : (3203024200596511903/3125000000000000000 : ℝ) ≤ (1006136242914779/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3203024200596511903/3125000000000000000 : ℝ)^32 ≤ (1006136242914779/1000000000000000 : ℝ)^129 := by
      have hnat : (3203024200596511903 : ℕ)^32*1000000000000000^129 ≤ 1006136242914779^129*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3203024200596511903 3125000000000000000 1006136242914779 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006136242914779/1000000000000000 : ℝ)) (X := (3203024200596511903/3125000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s8_corner0b : (1640524200596511903/1562500000000000000 : ℝ) ≤ (2024322194398953/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1640524200596511903/1562500000000000000 : ℝ)^32 ≤ (2024322194398953/2000000000000000 : ℝ)^129 := by
      have hnat : (1640524200596511903 : ℕ)^32*2000000000000000^129 ≤ 2024322194398953^129*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1640524200596511903 1562500000000000000 2024322194398953 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2024322194398953/2000000000000000 : ℝ)) (X := (1640524200596511903/1562500000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s8_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6136242914779/400360000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2409941713879/160144000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (10009/25000 : ℝ)) (alpha := (6136242914779/400360000000000 : ℝ)) (beta := (2409941713879/160144000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow0,s8_corner0a]) (by linarith only [s8_pow0,s8_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10009/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6136242914779/400360000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2409941713879/160144000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s8_pow1 : (20277/50000 : ℝ) ^ (129/32 : ℝ) ≤ (2629576684348389799/100000000000000000000 : ℝ) := by
    have hpowers : (20277/50000 : ℝ)^129 ≤ (2629576684348389799/100000000000000000000 : ℝ)^32 := by
      have hnat : (20277 : ℕ)^129*100000000000000000000^32 ≤ 2629576684348389799^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20277 50000 2629576684348389799 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20277/50000 : ℝ)) (X := (2629576684348389799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s8_corner1a : (102629576684348389799/100000000000000000000 : ℝ) ≤ (10064594649015971/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (102629576684348389799/100000000000000000000 : ℝ)^32 ≤ (10064594649015971/10000000000000000 : ℝ)^129 := by
      have hnat : (102629576684348389799 : ℕ)^32*10000000000000000^129 ≤ 10064594649015971^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102629576684348389799 100000000000000000000 10064594649015971 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064594649015971/10000000000000000 : ℝ)) (X := (102629576684348389799/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s8_corner1b : (52629576684348389799/50000000000000000000 : ℝ) ≤ (2531989133635699/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (52629576684348389799/50000000000000000000 : ℝ)^32 ≤ (2531989133635699/2500000000000000 : ℝ)^129 := by
      have hnat : (52629576684348389799 : ℕ)^32*2500000000000000^129 ≤ 2531989133635699^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52629576684348389799 50000000000000000000 2531989133635699 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2531989133635699/2500000000000000 : ℝ)) (X := (52629576684348389799/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s8_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(64594649015971/4055400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2534475421073/162216000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (20277/50000 : ℝ)) (alpha := (64594649015971/4055400000000000 : ℝ)) (beta := (2534475421073/162216000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow1,s8_corner1a]) (by linarith only [s8_pow1,s8_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (20277/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(64594649015971/4055400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2534475421073/162216000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s8_pow2 : (38663/100000 : ℝ) ^ (129/32 : ℝ) ≤ (542282004132726161/25000000000000000000 : ℝ) := by
    have hpowers : (38663/100000 : ℝ)^129 ≤ (542282004132726161/25000000000000000000 : ℝ)^32 := by
      have hnat : (38663 : ℕ)^129*25000000000000000000^32 ≤ 542282004132726161^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38663 100000 542282004132726161 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38663/100000 : ℝ)) (X := (542282004132726161/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s8_corner2a : (25542282004132726161/25000000000000000000 : ℝ) ≤ (2010674897505733/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25542282004132726161/25000000000000000000 : ℝ)^32 ≤ (2010674897505733/2000000000000000 : ℝ)^129 := by
      have hnat : (25542282004132726161 : ℕ)^32*2000000000000000^129 ≤ 2010674897505733^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25542282004132726161 25000000000000000000 2010674897505733 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010674897505733/2000000000000000 : ℝ)) (X := (25542282004132726161/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s8_corner2b : (13042282004132726161/12500000000000000000 : ℝ) ≤ (202118071440207/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13042282004132726161/12500000000000000000 : ℝ)^32 ≤ (202118071440207/200000000000000 : ℝ)^129 := by
      have hnat : (13042282004132726161 : ℕ)^32*200000000000000^129 ≤ 202118071440207^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13042282004132726161 12500000000000000000 202118071440207 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202118071440207/200000000000000 : ℝ)) (X := (13042282004132726161/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s8_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(10674897505733/773260000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(10505816896337/773260000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (38663/100000 : ℝ)) (alpha := (10674897505733/773260000000000 : ℝ)) (beta := (10505816896337/773260000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s8_pow2,s8_corner2a]) (by linarith only [s8_pow2,s8_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38663/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s7_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(10674897505733/773260000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(10505816896337/773260000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s8_0 : ((-1994101433/10000000000 : ℝ)*X 0 0+(5385511667/10000000000 : ℝ)*X 0 1+(5405709907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_1 : ((1346530939/2500000000 : ℝ)*X 1 0+(-499806033/2500000000 : ℝ)*X 1 1+(5401397509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_2 : ((5402007987/10000000000 : ℝ)*X 2 0+(539859573/1000000000 : ℝ)*X 2 1+(-1981108537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_6 : ((4373068641/10000000000 : ℝ)*X 0 0+(34147683/78125000 : ℝ)*X 0 1+(4361272627/10000000000 : ℝ)*X 0 2+(4373068641/10000000000 : ℝ)*X 1 0+(34147683/78125000 : ℝ)*X 1 1+(4361272627/10000000000 : ℝ)*X 1 2+(4373068641/10000000000 : ℝ)*X 2 0+(34147683/78125000 : ℝ)*X 2 1+(4361272627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_7 : ((-379560193/2000000000 : ℝ)*X 0 0+(4651160957/10000000000 : ℝ)*X 0 1+(123479913/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_8 : ((126902793/250000000 : ℝ)*X 1 0+(-646117273/5000000000 : ℝ)*X 1 1+(1233929591/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_9 : ((4913780557/10000000000 : ℝ)*X 2 0+(6336513033/10000000000 : ℝ)*X 2 1+(-316335617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_13 : ((4505951927/10000000000 : ℝ)*X 0 0+(2767422561/5000000000 : ℝ)*X 0 1+(2931870467/10000000000 : ℝ)*X 0 2+(4505951927/10000000000 : ℝ)*X 1 0+(2767422561/5000000000 : ℝ)*X 1 1+(2931870467/10000000000 : ℝ)*X 1 2+(4505951927/10000000000 : ℝ)*X 2 0+(2767422561/5000000000 : ℝ)*X 2 1+(2931870467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_14 : ((-1287334881/10000000000 : ℝ)*X 0 0+(5083554319/10000000000 : ℝ)*X 0 1+(6165601661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_15 : ((4666992219/10000000000 : ℝ)*X 1 0+(-1895293231/10000000000 : ℝ)*X 1 1+(3080628117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_16 : ((6161395611/10000000000 : ℝ)*X 2 0+(5096697727/10000000000 : ℝ)*X 2 1+(-1273735151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_20 : ((5856398927/10000000000 : ℝ)*X 0 0+(4139587811/10000000000 : ℝ)*X 0 1+(147415431/500000000 : ℝ)*X 0 2+(5856398927/10000000000 : ℝ)*X 1 0+(4139587811/10000000000 : ℝ)*X 1 1+(147415431/500000000 : ℝ)*X 1 2+(5856398927/10000000000 : ℝ)*X 2 0+(4139587811/10000000000 : ℝ)*X 2 1+(147415431/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_21 : ((-617292661/5000000000 : ℝ)*X 0 0+(1167060389/2000000000 : ℝ)*X 0 1+(546117507/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_22 : ((1239622011/2000000000 : ℝ)*X 1 0+(-1230217201/10000000000 : ℝ)*X 1 1+(2542555233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_23 : ((36065867/78125000 : ℝ)*X 2 0+(6220165071/10000000000 : ℝ)*X 2 1+(-1876297269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s8_27 : ((1496706589/2500000000 : ℝ)*X 0 0+(1782527181/5000000000 : ℝ)*X 0 1+(1700205341/5000000000 : ℝ)*X 0 2+(1496706589/2500000000 : ℝ)*X 1 0+(1782527181/5000000000 : ℝ)*X 1 1+(1700205341/5000000000 : ℝ)*X 1 2+(1496706589/2500000000 : ℝ)*X 2 0+(1782527181/5000000000 : ℝ)*X 2 1+(1700205341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s8_s8_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s8_0 : (0 : ℝ) ≤ ((3839/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3839/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (441969272900577724701581671/113721046911000000000000000000000 : ℝ) := by norm_num
    linear_combination (119401031871/1000000000000 : ℝ)*(base60) + (1264026098143/250000000000 : ℝ)*(major_s8_0) + (1264026098143/250000000000 : ℝ)*(major_s8_1) + (1264026098143/250000000000 : ℝ)*(major_s8_2) + (230951/25000000000 : ℝ)*(sp_s8_0) + (54657/250000000000 : ℝ)*(sp_s8_2) + (5503603/500000000000 : ℝ)*(sp_s8_6) + (3347069126777/500000000000 : ℝ)*(sp_s8_7) + (209191823953/31250000000 : ℝ)*(sp_s8_8) + (6694136299201/1000000000000 : ℝ)*(sp_s8_9) + (3418030955269/1000000000000 : ℝ)*(sp_s8_13) + (18035593/1000000000000 : ℝ)*(sp_s8_14) + (27160691/1000000000000 : ℝ)*(sp_s8_15) + (14504679/500000000000 : ℝ)*(sp_s8_23) + (136721678499/40000000000 : ℝ)*(f.failure) + (6694165527187/1000000000000 : ℝ)*(f.sum) + (157364072024570807/1704281850000000000000000000000 : ℝ)*base62 + (7002687417887/16810000000000000000000000 : ℝ)*base65 + (25645664137969/202770000000000000000000000 : ℝ)*base67 + (1862725533/16416015625000000000000 : ℝ)*base68 + (35700750128609969/84125645000000000000000000000 : ℝ)*base71 + (30683645078623/200180000000000000000000000 : ℝ)*base73 + (144339530647003/1013850000000000000000000000 : ℝ)*base75 + (101336171997/625562500000000000000000 : ℝ)*base77 + (691148238522580361/4059049860000000000000000000000 : ℝ)*base79 + (481/1000000000000000 : ℝ)*base86 + (481/1000000000000000 : ℝ)*base88 + (481/1000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s8_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31007/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (217852863153569147959987519247/34874454386040000000000000000000000 : ℝ) := by norm_num
    linear_combination (168469/100000000000 : ℝ)*(base60) + (5109030333219/1000000000000 : ℝ)*(major_s8_0) + (5109030333219/1000000000000 : ℝ)*(major_s8_1) + (5109030333219/1000000000000 : ℝ)*(major_s8_2) + (4862639/1000000000000 : ℝ)*(sp_s8_0) + (15482837/1000000000000 : ℝ)*(sp_s8_1) + (4049867/100000000000 : ℝ)*(sp_s8_2) + (5600989/125000000000 : ℝ)*(sp_s8_7) + (23304827/1000000000000 : ℝ)*(sp_s8_8) + (10569043449/1562500000 : ℝ)*(sp_s8_14) + (6764198690247/1000000000000 : ℝ)*(sp_s8_15) + (3382098489621/500000000000 : ℝ)*(sp_s8_16) + (3453774298771/1000000000000 : ℝ)*(sp_s8_20) + (9361497/200000000000 : ℝ)*(sp_s8_27) + (215863819141/62500000000 : ℝ)*(f.failure) + (845529684739/125000000000 : ℝ)*(f.sum) + (5240886158790515641/52264643400000000000000000000000 : ℝ)*base62 + (174247367070103/154652000000000000000000000 : ℝ)*base65 + (272617627893217/270360000000000000000000000 : ℝ)*base67 + (131163746770839/154652000000000000000000000 : ℝ)*base69 + (2521336548700749293/15479118680000000000000000000000 : ℝ)*base71 + (814224713299273/800720000000000000000000000 : ℝ)*base73 + (706597612576663/1351800000000000000000000000 : ℝ)*base75 + (171561319235741/400360000000000000000000000 : ℝ)*base77 + (773577891980884121/5412066480000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (2733/3125000000000000 : ℝ)*base86 + (2733/3125000000000000 : ℝ)*base88 + (2733/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s8_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14821/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14821/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17710439954203958193210987/1934889835000000000000000000000 : ℝ) := by norm_num
    linear_combination (232657879811/1000000000000 : ℝ)*(base40) + (1341373/500000000000 : ℝ)*(base50) + (2363712832607/500000000000 : ℝ)*(major_s8_0) + (2363712832607/500000000000 : ℝ)*(major_s8_1) + (2363712832607/500000000000 : ℝ)*(major_s8_2) + (42720229/500000000000 : ℝ)*(sp_s8_0) + (161897/1953125000 : ℝ)*(sp_s8_1) + (27510817/500000000000 : ℝ)*(sp_s8_2) + (16881117/500000000000 : ℝ)*(sp_s8_9) + (18346481/200000000000 : ℝ)*(sp_s8_20) + (6258915197399/1000000000000 : ℝ)*(sp_s8_21) + (6258917746593/1000000000000 : ℝ)*(sp_s8_22) + (6258911853989/1000000000000 : ℝ)*(sp_s8_23) + (399469488637/125000000000 : ℝ)*(sp_s8_27) + (3195847641501/1000000000000 : ℝ)*(f.failure) + (6259000637857/1000000000000 : ℝ)*(f.sum) + (8825855714604695609/78396965100000000000000000000000 : ℝ)*base62 + (19611951842527/77326000000000000000000000 : ℝ)*base65 + (117978685897523/405540000000000000000000000 : ℝ)*base67 + (93715685469901/386630000000000000000000000 : ℝ)*base69 + (408572916399196557/7739559340000000000000000000000 : ℝ)*base71 + (67080042084469/400360000000000000000000000 : ℝ)*base73 + (477945553906727/2027700000000000000000000000 : ℝ)*base75 + (80484585517429/200180000000000000000000000 : ℝ)*base77 + (1491598686493690397/8118099720000000000000000000000 : ℝ)*base78 + (1519/25000000000000000 : ℝ)*base86 + (1519/25000000000000000 : ℝ)*base88 + (1519/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s8_0,ratio_s8_1,ratio_s8_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev7 : (0 : ℝ) ≤ ((10009/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10009/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38663/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3839/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3839/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31007/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31007/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14821/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14821/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301063_s8 p hpa hpb X hX hprev7

#print axioms solution
