-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c321055_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:41:26.675471+00:00
-- url     : https://prove2.me/submissions/17e597be-aa50-4397-8056-93a376ba1d98

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
theorem collision_support_c321055_s0_s0_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-193434953/2000000000 : ℝ)*x 0 + (5768219223/10000000000 : ℝ)*x 1 + (5167351763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193434953/2000000000 : ℝ)^41 ≤ (2744964730293/50000000000000 : ℝ)^33 := by
    have hnat : (193434953 : ℕ)^41*50000000000000^33 ≤ 2744964730293^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193434953 2000000000 2744964730293 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5768219223/10000000000 : ℝ)^41 ≤ (50479202682437/100000000000000 : ℝ)^33 := by
    have hnat : (5768219223 : ℕ)^41*100000000000000^33 ≤ 50479202682437^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5768219223 10000000000 50479202682437 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167351763/10000000000 : ℝ)^41 ≤ (275192923987/625000000000 : ℝ)^33 := by
    have hnat : (5167351763 : ℕ)^41*625000000000^33 ≤ 275192923987^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167351763 10000000000 275192923987 625000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-193434953/2000000000 : ℝ), (5768219223/10000000000 : ℝ), (5167351763/10000000000 : ℝ)] ![(2744964730293/50000000000000 : ℝ), (50479202682437/100000000000000 : ℝ), (275192923987/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-193434953/2000000000 : ℝ)|^41 ≤ (2744964730293/50000000000000 : ℝ)^33
        have hw : |(-193434953/2000000000 : ℝ)|=(193434953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5768219223/10000000000 : ℝ)|^41 ≤ (50479202682437/100000000000000 : ℝ)^33
        have hw : |(5768219223/10000000000 : ℝ)|=(5768219223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167351763/10000000000 : ℝ)|^41 ≤ (275192923987/625000000000 : ℝ)^33
        have hw : |(5167351763/10000000000 : ℝ)|=(5167351763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (24061011/50000000 : ℝ)*x 0 + (-1394563/1250000000 : ℝ)*x 1 + (6600000071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24061011/50000000 : ℝ)^41 ≤ (40302902136537/100000000000000 : ℝ)^33 := by
    have hnat : (24061011 : ℕ)^41*100000000000000^33 ≤ 40302902136537^33*50000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24061011 50000000 40302902136537 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394563/1250000000 : ℝ)^41 ≤ (536682429/2500000000000 : ℝ)^33 := by
    have hnat : (1394563 : ℕ)^41*2500000000000^33 ≤ 536682429^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394563 1250000000 536682429 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6600000071/10000000000 : ℝ)^41 ≤ (59675630556177/100000000000000 : ℝ)^33 := by
    have hnat : (6600000071 : ℕ)^41*100000000000000^33 ≤ 59675630556177^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6600000071 10000000000 59675630556177 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24061011/50000000 : ℝ), (-1394563/1250000000 : ℝ), (6600000071/10000000000 : ℝ)] ![(40302902136537/100000000000000 : ℝ), (536682429/2500000000000 : ℝ), (59675630556177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24061011/50000000 : ℝ)|^41 ≤ (40302902136537/100000000000000 : ℝ)^33
        have hw : |(24061011/50000000 : ℝ)|=(24061011/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394563/1250000000 : ℝ)|^41 ≤ (536682429/2500000000000 : ℝ)^33
        have hw : |(-1394563/1250000000 : ℝ)|=(1394563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6600000071/10000000000 : ℝ)|^41 ≤ (59675630556177/100000000000000 : ℝ)^33
        have hw : |(6600000071/10000000000 : ℝ)|=(6600000071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-954986711/2500000000 : ℝ)*x 0 + (107079779/400000000 : ℝ)*x 1 + (359484473/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954986711/2500000000 : ℝ)^41 ≤ (15125435440347/50000000000000 : ℝ)^33 := by
    have hnat : (954986711 : ℕ)^41*50000000000000^33 ≤ 15125435440347^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954986711 2500000000 15125435440347 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107079779/400000000 : ℝ)^41 ≤ (4862228405977/25000000000000 : ℝ)^33 := by
    have hnat : (107079779 : ℕ)^41*25000000000000^33 ≤ 4862228405977^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107079779 400000000 4862228405977 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359484473/625000000 : ℝ)^41 ≤ (25150107739059/50000000000000 : ℝ)^33 := by
    have hnat : (359484473 : ℕ)^41*50000000000000^33 ≤ 25150107739059^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359484473 625000000 25150107739059 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954986711/2500000000 : ℝ), (107079779/400000000 : ℝ), (359484473/625000000 : ℝ)] ![(15125435440347/50000000000000 : ℝ), (4862228405977/25000000000000 : ℝ), (25150107739059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954986711/2500000000 : ℝ)|^41 ≤ (15125435440347/50000000000000 : ℝ)^33
        have hw : |(-954986711/2500000000 : ℝ)|=(954986711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107079779/400000000 : ℝ)|^41 ≤ (4862228405977/25000000000000 : ℝ)^33
        have hw : |(107079779/400000000 : ℝ)|=(107079779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(359484473/625000000 : ℝ)|^41 ≤ (25150107739059/50000000000000 : ℝ)^33
        have hw : |(359484473/625000000 : ℝ)|=(359484473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (30898783/156250000 : ℝ)*x 0 + (-44877/5000000000 : ℝ)*x 1 + (4455338669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30898783/156250000 : ℝ)^41 ≤ (1335008710823/10000000000000 : ℝ)^33 := by
    have hnat : (30898783 : ℕ)^41*10000000000000^33 ≤ 1335008710823^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30898783 156250000 1335008710823 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44877/5000000000 : ℝ)^41 ≤ (26823887/50000000000000 : ℝ)^33 := by
    have hnat : (44877 : ℕ)^41*50000000000000^33 ≤ 26823887^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44877 5000000000 26823887 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4455338669/5000000000 : ℝ)^41 ≤ (86649859240931/100000000000000 : ℝ)^33 := by
    have hnat : (4455338669 : ℕ)^41*100000000000000^33 ≤ 86649859240931^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455338669 5000000000 86649859240931 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30898783/156250000 : ℝ), (-44877/5000000000 : ℝ), (4455338669/5000000000 : ℝ)] ![(1335008710823/10000000000000 : ℝ), (26823887/50000000000000 : ℝ), (86649859240931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30898783/156250000 : ℝ)|^41 ≤ (1335008710823/10000000000000 : ℝ)^33
        have hw : |(30898783/156250000 : ℝ)|=(30898783/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44877/5000000000 : ℝ)|^41 ≤ (26823887/50000000000000 : ℝ)^33
        have hw : |(-44877/5000000000 : ℝ)|=(44877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4455338669/5000000000 : ℝ)|^41 ≤ (86649859240931/100000000000000 : ℝ)^33
        have hw : |(4455338669/5000000000 : ℝ)|=(4455338669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (876001869/5000000000 : ℝ)*x 0 + (2189419809/2500000000 : ℝ)*x 1 + (-705424573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (876001869/5000000000 : ℝ)^41 ≤ (11485491394919/100000000000000 : ℝ)^33 := by
    have hnat : (876001869 : ℕ)^41*100000000000000^33 ≤ 11485491394919^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876001869 5000000000 11485491394919 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189419809/2500000000 : ℝ)^41 ≤ (84805250189717/100000000000000 : ℝ)^33 := by
    have hnat : (2189419809 : ℕ)^41*100000000000000^33 ≤ 84805250189717^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189419809 2500000000 84805250189717 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705424573/10000000000 : ℝ)^41 ≤ (3709258402507/100000000000000 : ℝ)^33 := by
    have hnat : (705424573 : ℕ)^41*100000000000000^33 ≤ 3709258402507^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705424573 10000000000 3709258402507 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(876001869/5000000000 : ℝ), (2189419809/2500000000 : ℝ), (-705424573/10000000000 : ℝ)] ![(11485491394919/100000000000000 : ℝ), (84805250189717/100000000000000 : ℝ), (3709258402507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(876001869/5000000000 : ℝ)|^41 ≤ (11485491394919/100000000000000 : ℝ)^33
        have hw : |(876001869/5000000000 : ℝ)|=(876001869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2189419809/2500000000 : ℝ)|^41 ≤ (84805250189717/100000000000000 : ℝ)^33
        have hw : |(2189419809/2500000000 : ℝ)|=(2189419809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-705424573/10000000000 : ℝ)|^41 ≤ (3709258402507/100000000000000 : ℝ)^33
        have hw : |(-705424573/10000000000 : ℝ)|=(705424573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3727767811/10000000000 : ℝ)*x 0 + (1820773131/2500000000 : ℝ)*x 1 + (313990739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3727767811/10000000000 : ℝ)^41 ≤ (7336647878303/25000000000000 : ℝ)^33 := by
    have hnat : (3727767811 : ℕ)^41*25000000000000^33 ≤ 7336647878303^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727767811 10000000000 7336647878303 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820773131/2500000000 : ℝ)^41 ≤ (67443149956129/100000000000000 : ℝ)^33 := by
    have hnat : (1820773131 : ℕ)^41*100000000000000^33 ≤ 67443149956129^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820773131 2500000000 67443149956129 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313990739/5000000000 : ℝ)^41 ≤ (3210258515543/100000000000000 : ℝ)^33 := by
    have hnat : (313990739 : ℕ)^41*100000000000000^33 ≤ 3210258515543^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313990739 5000000000 3210258515543 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3727767811/10000000000 : ℝ), (1820773131/2500000000 : ℝ), (313990739/5000000000 : ℝ)] ![(7336647878303/25000000000000 : ℝ), (67443149956129/100000000000000 : ℝ), (3210258515543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3727767811/10000000000 : ℝ)|^41 ≤ (7336647878303/25000000000000 : ℝ)^33
        have hw : |(3727767811/10000000000 : ℝ)|=(3727767811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1820773131/2500000000 : ℝ)|^41 ≤ (67443149956129/100000000000000 : ℝ)^33
        have hw : |(1820773131/2500000000 : ℝ)|=(1820773131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313990739/5000000000 : ℝ)|^41 ≤ (3210258515543/100000000000000 : ℝ)^33
        have hw : |(313990739/5000000000 : ℝ)|=(313990739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-267983017/5000000000 : ℝ)*x 0 + (1623843127/5000000000 : ℝ)*x 1 + (7731201709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267983017/5000000000 : ℝ)^41 ≤ (2636630871361/100000000000000 : ℝ)^33 := by
    have hnat : (267983017 : ℕ)^41*100000000000000^33 ≤ 2636630871361^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267983017 5000000000 2636630871361 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1623843127/5000000000 : ℝ)^41 ≤ (4945358454519/20000000000000 : ℝ)^33 := by
    have hnat : (1623843127 : ℕ)^41*20000000000000^33 ≤ 4945358454519^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623843127 5000000000 4945358454519 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7731201709/10000000000 : ℝ)^41 ≤ (72636576846557/100000000000000 : ℝ)^33 := by
    have hnat : (7731201709 : ℕ)^41*100000000000000^33 ≤ 72636576846557^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7731201709 10000000000 72636576846557 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267983017/5000000000 : ℝ), (1623843127/5000000000 : ℝ), (7731201709/10000000000 : ℝ)] ![(2636630871361/100000000000000 : ℝ), (4945358454519/20000000000000 : ℝ), (72636576846557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267983017/5000000000 : ℝ)|^41 ≤ (2636630871361/100000000000000 : ℝ)^33
        have hw : |(-267983017/5000000000 : ℝ)|=(267983017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1623843127/5000000000 : ℝ)|^41 ≤ (4945358454519/20000000000000 : ℝ)^33
        have hw : |(1623843127/5000000000 : ℝ)|=(1623843127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7731201709/10000000000 : ℝ)|^41 ≤ (72636576846557/100000000000000 : ℝ)^33
        have hw : |(7731201709/10000000000 : ℝ)|=(7731201709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (82656001/1000000000 : ℝ)*x 0 + (-100441761/5000000000 : ℝ)*x 1 + (4785766299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82656001/1000000000 : ℝ)^41 ≤ (4516431772319/100000000000000 : ℝ)^33 := by
    have hnat : (82656001 : ℕ)^41*100000000000000^33 ≤ 4516431772319^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82656001 1000000000 4516431772319 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100441761/5000000000 : ℝ)^41 ≤ (389499477467/50000000000000 : ℝ)^33 := by
    have hnat : (100441761 : ℕ)^41*50000000000000^33 ≤ 389499477467^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100441761 5000000000 389499477467 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785766299/5000000000 : ℝ)^41 ≤ (94704569259573/100000000000000 : ℝ)^33 := by
    have hnat : (4785766299 : ℕ)^41*100000000000000^33 ≤ 94704569259573^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785766299 5000000000 94704569259573 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82656001/1000000000 : ℝ), (-100441761/5000000000 : ℝ), (4785766299/5000000000 : ℝ)] ![(4516431772319/100000000000000 : ℝ), (389499477467/50000000000000 : ℝ), (94704569259573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82656001/1000000000 : ℝ)|^41 ≤ (4516431772319/100000000000000 : ℝ)^33
        have hw : |(82656001/1000000000 : ℝ)|=(82656001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100441761/5000000000 : ℝ)|^41 ≤ (389499477467/50000000000000 : ℝ)^33
        have hw : |(-100441761/5000000000 : ℝ)|=(100441761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785766299/5000000000 : ℝ)|^41 ≤ (94704569259573/100000000000000 : ℝ)^33
        have hw : |(4785766299/5000000000 : ℝ)|=(4785766299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3711612899/5000000000 : ℝ)*x 0 + (1813333847/5000000000 : ℝ)*x 1 + (-65831829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3711612899/5000000000 : ℝ)^41 ≤ (34529572512183/50000000000000 : ℝ)^33 := by
    have hnat : (3711612899 : ℕ)^41*50000000000000^33 ≤ 34529572512183^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711612899 5000000000 34529572512183 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1813333847/5000000000 : ℝ)^41 ≤ (354512685389/1250000000000 : ℝ)^33 := by
    have hnat : (1813333847 : ℕ)^41*1250000000000^33 ≤ 354512685389^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813333847 5000000000 354512685389 1250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65831829/1250000000 : ℝ)^41 ≤ (16124000851/625000000000 : ℝ)^33 := by
    have hnat : (65831829 : ℕ)^41*625000000000^33 ≤ 16124000851^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65831829 1250000000 16124000851 625000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3711612899/5000000000 : ℝ), (1813333847/5000000000 : ℝ), (-65831829/1250000000 : ℝ)] ![(34529572512183/50000000000000 : ℝ), (354512685389/1250000000000 : ℝ), (16124000851/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3711612899/5000000000 : ℝ)|^41 ≤ (34529572512183/50000000000000 : ℝ)^33
        have hw : |(3711612899/5000000000 : ℝ)|=(3711612899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1813333847/5000000000 : ℝ)|^41 ≤ (354512685389/1250000000000 : ℝ)^33
        have hw : |(1813333847/5000000000 : ℝ)|=(1813333847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65831829/1250000000 : ℝ)|^41 ≤ (16124000851/625000000000 : ℝ)^33
        have hw : |(-65831829/1250000000 : ℝ)|=(65831829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (539160269/625000000 : ℝ)*x 0 + (52981979/250000000 : ℝ)*x 1 + (233346849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539160269/625000000 : ℝ)^41 ≤ (16646134616223/20000000000000 : ℝ)^33 := by
    have hnat : (539160269 : ℕ)^41*20000000000000^33 ≤ 16646134616223^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539160269 625000000 16646134616223 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52981979/250000000 : ℝ)^41 ≤ (3637306118407/25000000000000 : ℝ)^33 := by
    have hnat : (52981979 : ℕ)^41*25000000000000^33 ≤ 3637306118407^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52981979 250000000 3637306118407 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233346849/5000000000 : ℝ)^41 ≤ (1110051214351/50000000000000 : ℝ)^33 := by
    have hnat : (233346849 : ℕ)^41*50000000000000^33 ≤ 1110051214351^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233346849 5000000000 1110051214351 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539160269/625000000 : ℝ), (52981979/250000000 : ℝ), (233346849/5000000000 : ℝ)] ![(16646134616223/20000000000000 : ℝ), (3637306118407/25000000000000 : ℝ), (1110051214351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539160269/625000000 : ℝ)|^41 ≤ (16646134616223/20000000000000 : ℝ)^33
        have hw : |(539160269/625000000 : ℝ)|=(539160269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52981979/250000000 : ℝ)|^41 ≤ (3637306118407/25000000000000 : ℝ)^33
        have hw : |(52981979/250000000 : ℝ)|=(52981979/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233346849/5000000000 : ℝ)|^41 ≤ (1110051214351/50000000000000 : ℝ)^33
        have hw : |(233346849/5000000000 : ℝ)|=(233346849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-31872241/500000000 : ℝ)*x 0 + (4090687033/5000000000 : ℝ)*x 1 + (1302521881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31872241/500000000 : ℝ)^41 ≤ (8176181189/250000000000 : ℝ)^33 := by
    have hnat : (31872241 : ℕ)^41*250000000000^33 ≤ 8176181189^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31872241 500000000 8176181189 250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4090687033/5000000000 : ℝ)^41 ≤ (38963972105421/50000000000000 : ℝ)^33 := by
    have hnat : (4090687033 : ℕ)^41*50000000000000^33 ≤ 38963972105421^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090687033 5000000000 38963972105421 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302521881/5000000000 : ℝ)^41 ≤ (9400791646193/50000000000000 : ℝ)^33 := by
    have hnat : (1302521881 : ℕ)^41*50000000000000^33 ≤ 9400791646193^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302521881 5000000000 9400791646193 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31872241/500000000 : ℝ), (4090687033/5000000000 : ℝ), (1302521881/5000000000 : ℝ)] ![(8176181189/250000000000 : ℝ), (38963972105421/50000000000000 : ℝ), (9400791646193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31872241/500000000 : ℝ)|^41 ≤ (8176181189/250000000000 : ℝ)^33
        have hw : |(-31872241/500000000 : ℝ)|=(31872241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4090687033/5000000000 : ℝ)|^41 ≤ (38963972105421/50000000000000 : ℝ)^33
        have hw : |(4090687033/5000000000 : ℝ)|=(4090687033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1302521881/5000000000 : ℝ)|^41 ≤ (9400791646193/50000000000000 : ℝ)^33
        have hw : |(1302521881/5000000000 : ℝ)|=(1302521881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (186016371/250000000 : ℝ)*x 0 + (-5249719/5000000000 : ℝ)*x 1 + (120859337/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186016371/250000000 : ℝ)^41 ≤ (69260654497153/100000000000000 : ℝ)^33 := by
    have hnat : (186016371 : ℕ)^41*100000000000000^33 ≤ 69260654497153^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186016371 250000000 69260654497153 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5249719/5000000000 : ℝ)^41 ≤ (19907855993/100000000000000 : ℝ)^33 := by
    have hnat : (5249719 : ℕ)^41*100000000000000^33 ≤ 19907855993^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5249719 5000000000 19907855993 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120859337/312500000 : ℝ)^41 ≤ (30719437645461/100000000000000 : ℝ)^33 := by
    have hnat : (120859337 : ℕ)^41*100000000000000^33 ≤ 30719437645461^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120859337 312500000 30719437645461 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(186016371/250000000 : ℝ), (-5249719/5000000000 : ℝ), (120859337/312500000 : ℝ)] ![(69260654497153/100000000000000 : ℝ), (19907855993/100000000000000 : ℝ), (30719437645461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(186016371/250000000 : ℝ)|^41 ≤ (69260654497153/100000000000000 : ℝ)^33
        have hw : |(186016371/250000000 : ℝ)|=(186016371/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5249719/5000000000 : ℝ)|^41 ≤ (19907855993/100000000000000 : ℝ)^33
        have hw : |(-5249719/5000000000 : ℝ)|=(5249719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(120859337/312500000 : ℝ)|^41 ≤ (30719437645461/100000000000000 : ℝ)^33
        have hw : |(120859337/312500000 : ℝ)|=(120859337/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (628859003/10000000000 : ℝ)*x 0 + (8946525583/10000000000 : ℝ)*x 1 + (-764681341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628859003/10000000000 : ℝ)^41 ≤ (803958222423/25000000000000 : ℝ)^33 := by
    have hnat : (628859003 : ℕ)^41*25000000000000^33 ≤ 803958222423^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628859003 10000000000 803958222423 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8946525583/10000000000 : ℝ)^41 ≤ (87083176986113/100000000000000 : ℝ)^33 := by
    have hnat : (8946525583 : ℕ)^41*100000000000000^33 ≤ 87083176986113^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8946525583 10000000000 87083176986113 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764681341/5000000000 : ℝ)^41 ≤ (9700990109079/100000000000000 : ℝ)^33 := by
    have hnat : (764681341 : ℕ)^41*100000000000000^33 ≤ 9700990109079^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764681341 5000000000 9700990109079 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(628859003/10000000000 : ℝ), (8946525583/10000000000 : ℝ), (-764681341/5000000000 : ℝ)] ![(803958222423/25000000000000 : ℝ), (87083176986113/100000000000000 : ℝ), (9700990109079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(628859003/10000000000 : ℝ)|^41 ≤ (803958222423/25000000000000 : ℝ)^33
        have hw : |(628859003/10000000000 : ℝ)|=(628859003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8946525583/10000000000 : ℝ)|^41 ≤ (87083176986113/100000000000000 : ℝ)^33
        have hw : |(8946525583/10000000000 : ℝ)|=(8946525583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764681341/5000000000 : ℝ)|^41 ≤ (9700990109079/100000000000000 : ℝ)^33
        have hw : |(-764681341/5000000000 : ℝ)|=(764681341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s0_s0_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2071168389/2500000000 : ℝ)*x 0 + (1992399971/10000000000 : ℝ)*x 1 + (245250223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071168389/2500000000 : ℝ)^41 ≤ (19788067583209/25000000000000 : ℝ)^33 := by
    have hnat : (2071168389 : ℕ)^41*25000000000000^33 ≤ 19788067583209^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071168389 2500000000 19788067583209 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992399971/10000000000 : ℝ)^41 ≤ (538999550911/4000000000000 : ℝ)^33 := by
    have hnat : (1992399971 : ℕ)^41*4000000000000^33 ≤ 538999550911^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992399971 10000000000 538999550911 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245250223/2000000000 : ℝ)^41 ≤ (7372740878393/100000000000000 : ℝ)^33 := by
    have hnat : (245250223 : ℕ)^41*100000000000000^33 ≤ 7372740878393^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245250223 2000000000 7372740878393 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2071168389/2500000000 : ℝ), (1992399971/10000000000 : ℝ), (245250223/2000000000 : ℝ)] ![(19788067583209/25000000000000 : ℝ), (538999550911/4000000000000 : ℝ), (7372740878393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2071168389/2500000000 : ℝ)|^41 ≤ (19788067583209/25000000000000 : ℝ)^33
        have hw : |(2071168389/2500000000 : ℝ)|=(2071168389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1992399971/10000000000 : ℝ)|^41 ≤ (538999550911/4000000000000 : ℝ)^33
        have hw : |(1992399971/10000000000 : ℝ)|=(1992399971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(245250223/2000000000 : ℝ)|^41 ≤ (7372740878393/100000000000000 : ℝ)^33
        have hw : |(245250223/2000000000 : ℝ)|=(245250223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321055_s0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : (0 : ℝ) ≤ ((7267/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7267/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3477/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3477/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7073/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7073/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (168549/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(478111259889213/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (81/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^81 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^81*1^16 ≤ 1^16*1^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11467340684240883/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11467340684240883/10000000000000000 : ℝ)^81 := by
      have hnat : (2 : ℕ)^16*10000000000000000^81 ≤ 11467340684240883^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11467340684240883 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11467340684240883/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12423563204019309/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12423563204019309/10000000000000000 : ℝ)^81 := by
      have hnat : (3 : ℕ)^16*10000000000000000^81 ≤ 12423563204019309^81*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12423563204019309 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423563204019309/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1467340684240883/10000000000000000 : ℝ)) (beta := (478111259889213/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1467340684240883/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(478111259889213/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-193434953/2000000000 : ℝ)*X 0 0+(5768219223/10000000000 : ℝ)*X 0 1+(5167351763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((24061011/50000000 : ℝ)*X 1 0+(-1394563/1250000000 : ℝ)*X 1 1+(6600000071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-954986711/2500000000 : ℝ)*X 0 0+(107079779/400000000 : ℝ)*X 0 1+(359484473/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((30898783/156250000 : ℝ)*X 1 0+(-44877/5000000000 : ℝ)*X 1 1+(4455338669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((876001869/5000000000 : ℝ)*X 2 0+(2189419809/2500000000 : ℝ)*X 2 1+(-705424573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3727767811/10000000000 : ℝ)*X 0 0+(1820773131/2500000000 : ℝ)*X 0 1+(313990739/5000000000 : ℝ)*X 0 2+(3727767811/10000000000 : ℝ)*X 1 0+(1820773131/2500000000 : ℝ)*X 1 1+(313990739/5000000000 : ℝ)*X 1 2+(3727767811/10000000000 : ℝ)*X 2 0+(1820773131/2500000000 : ℝ)*X 2 1+(313990739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-267983017/5000000000 : ℝ)*X 0 0+(1623843127/5000000000 : ℝ)*X 0 1+(7731201709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((82656001/1000000000 : ℝ)*X 1 0+(-100441761/5000000000 : ℝ)*X 1 1+(4785766299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3711612899/5000000000 : ℝ)*X 2 0+(1813333847/5000000000 : ℝ)*X 2 1+(-65831829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((539160269/625000000 : ℝ)*X 0 0+(52981979/250000000 : ℝ)*X 0 1+(233346849/5000000000 : ℝ)*X 0 2+(539160269/625000000 : ℝ)*X 1 0+(52981979/250000000 : ℝ)*X 1 1+(233346849/5000000000 : ℝ)*X 1 2+(539160269/625000000 : ℝ)*X 2 0+(52981979/250000000 : ℝ)*X 2 1+(233346849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-31872241/500000000 : ℝ)*X 0 0+(4090687033/5000000000 : ℝ)*X 0 1+(1302521881/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((186016371/250000000 : ℝ)*X 1 0+(-5249719/5000000000 : ℝ)*X 1 1+(120859337/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((628859003/10000000000 : ℝ)*X 2 0+(8946525583/10000000000 : ℝ)*X 2 1+(-764681341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2071168389/2500000000 : ℝ)*X 0 0+(1992399971/10000000000 : ℝ)*X 0 1+(245250223/2000000000 : ℝ)*X 0 2+(2071168389/2500000000 : ℝ)*X 1 0+(1992399971/10000000000 : ℝ)*X 1 1+(245250223/2000000000 : ℝ)*X 1 2+(2071168389/2500000000 : ℝ)*X 2 0+(1992399971/10000000000 : ℝ)*X 2 1+(245250223/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((7267/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7267/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23267380695198040519029/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003327826639/1000000000000 : ℝ)*(base7) + (1028263/1000000000000 : ℝ)*(base49) + (693909051807/1000000000000 : ℝ)*(base53) + (1828337/1000000000000 : ℝ)*(base60) + (723393924989/500000000000 : ℝ)*(major_s0_0) + (723393924989/500000000000 : ℝ)*(major_s0_1) + (752878798171/1000000000000 : ℝ)*(major_s0_2) + (27637869/1000000000000 : ℝ)*(sp_s0_0) + (317257/62500000000 : ℝ)*(sp_s0_1) + (54742122061/62500000000 : ℝ)*(sp_s0_7) + (218974128683/250000000000 : ℝ)*(sp_s0_8) + (392452157303/250000000000 : ℝ)*(sp_s0_9) + (1763387006463/1000000000000 : ℝ)*(sp_s0_13) + (1573/781250000 : ℝ)*(sp_s0_23) + (47503698739/62500000000 : ℝ)*(f.failure) + (392452660663/250000000000 : ℝ)*(f.sum) + (313716158075567/10000000000000000000000000000 : ℝ)*base63 + (2499350952470577/5000000000000000000000000000 : ℝ)*base64 + (1643451304493657/2500000000000000000000000000 : ℝ)*base66 + (3329170373175007/10000000000000000000000000000 : ℝ)*base68 + (48662623815471/500000000000000000000000000 : ℝ)*base71 + (242073451743657/2500000000000000000000000000 : ℝ)*base73 + (2128427325374713/5000000000000000000000000000 : ℝ)*base74 + (3662878772874713/5000000000000000000000000000 : ℝ)*base76 + (520709879/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (907/1562500000000000 : ℝ)*base87 + (907/1562500000000000 : ℝ)*base89 + (907/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3477/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3477/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3113008540942619576301/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122408616851/125000000000 : ℝ)*(base7) + (15432461887/250000000000 : ℝ)*(base53) + (1024129/1000000000000 : ℝ)*(base59) + (140514335797/100000000000 : ℝ)*(major_s0_0) + (140514335797/100000000000 : ℝ)*(major_s0_1) + (671706755211/500000000000 : ℝ)*(major_s0_2) + (19169087/1000000000000 : ℝ)*(sp_s0_0) + (1600229/1000000000000 : ℝ)*(sp_s0_7) + (41526879/1000000000000 : ℝ)*(sp_s0_8) + (182521276981/125000000000 : ℝ)*(sp_s0_14) + (292029891657/200000000000 : ℝ)*(sp_s0_15) + (190240104089/125000000000 : ℝ)*(sp_s0_16) + (429361525421/250000000000 : ℝ)*(sp_s0_20) + (2195217/500000000000 : ℝ)*(sp_s0_27) + (73818155731/100000000000 : ℝ)*(f.failure) + (190240104089/125000000000 : ℝ)*(f.sum) + (300342915016233/1250000000000000000000000000 : ℝ)*base62 + (671458035061057/2500000000000000000000000000 : ℝ)*base64 + (164550751407761/500000000000000000000000000 : ℝ)*base66 + (2776398629508687/5000000000000000000000000000 : ℝ)*base68 + (753695970821641/5000000000000000000000000000 : ℝ)*base71 + (186370693642239/500000000000000000000000000 : ℝ)*base72 + (473675643811249/1000000000000000000000000000 : ℝ)*base74 + (467339000411249/1000000000000000000000000000 : ℝ)*base76 + (52949679/5000000000000000000000 : ℝ)*base78 + (457/625000000000000 : ℝ)*base87 + (457/625000000000000 : ℝ)*base89 + (457/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7073/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7073/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23941315575715225777899/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45635025589/40000000000 : ℝ)*(base7) + (1518001/1000000000000 : ℝ)*(base11) + (36039931791/1000000000000 : ℝ)*(base40) + (1673139/1000000000000 : ℝ)*(base43) + (25938521611/500000000000 : ℝ)*(base50) + (1378538858637/1000000000000 : ℝ)*(major_s0_0) + (689268592749/500000000000 : ℝ)*(major_s0_1) + (1378538858637/1000000000000 : ℝ)*(major_s0_2) + (42976761/1000000000000 : ℝ)*(sp_s0_9) + (4209303/200000000000 : ℝ)*(sp_s0_20) + (1391888090789/1000000000000 : ℝ)*(sp_s0_21) + (1391891281929/1000000000000 : ℝ)*(sp_s0_22) + (1391846632029/1000000000000 : ℝ)*(sp_s0_23) + (466264918927/250000000000 : ℝ)*(sp_s0_27) + (362102541249/500000000000 : ℝ)*(f.failure) + (1391891281929/1000000000000 : ℝ)*(f.sum) + (661964370274241/2000000000000000000000000000 : ℝ)*base63 + (774636882817319/5000000000000000000000000000 : ℝ)*base64 + (379975432116537/2500000000000000000000000000 : ℝ)*base66 + (1217299025056471/10000000000000000000000000000 : ℝ)*base69 + (3755676196578167/10000000000000000000000000000 : ℝ)*base70 + (1675042475182681/5000000000000000000000000000 : ℝ)*base73 + (1263327786657367/5000000000000000000000000000 : ℝ)*base75 + (6733200777943529/10000000000000000000000000000 : ℝ)*base76 + (2308816248449607/5000000000000000000000000000 : ℝ)*base79 + (159/390625000000000 : ℝ)*base86 + (159/390625000000000 : ℝ)*base88 + (159/390625000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : (0 : ℝ) ≤ ((7267/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7267/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3477/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3477/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7073/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7073/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c321055_s0 p hpa hpb X hX

#print axioms solution
