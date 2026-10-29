-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c321055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:41:56.170986+00:00
-- url     : https://prove2.me/submissions/348d5ead-35ca-4bf0-aa17-83064cca685e

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
theorem collision_support_c321055_s1_s1_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-32884129/200000000 : ℝ)*x 0 + (706270967/1250000000 : ℝ)*x 1 + (4801060133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32884129/200000000 : ℝ)^41 ≤ (10614148491033/100000000000000 : ℝ)^33 := by
    have hnat : (32884129 : ℕ)^41*100000000000000^33 ≤ 10614148491033^33*200000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32884129 200000000 10614148491033 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (706270967/1250000000 : ℝ)^41 ≤ (12299713853939/25000000000000 : ℝ)^33 := by
    have hnat : (706270967 : ℕ)^41*25000000000000^33 ≤ 12299713853939^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706270967 1250000000 12299713853939 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4801060133/10000000000 : ℝ)^41 ≤ (10046749017929/25000000000000 : ℝ)^33 := by
    have hnat : (4801060133 : ℕ)^41*25000000000000^33 ≤ 10046749017929^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801060133 10000000000 10046749017929 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32884129/200000000 : ℝ), (706270967/1250000000 : ℝ), (4801060133/10000000000 : ℝ)] ![(10614148491033/100000000000000 : ℝ), (12299713853939/25000000000000 : ℝ), (10046749017929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32884129/200000000 : ℝ)|^41 ≤ (10614148491033/100000000000000 : ℝ)^33
        have hw : |(-32884129/200000000 : ℝ)|=(32884129/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(706270967/1250000000 : ℝ)|^41 ≤ (12299713853939/25000000000000 : ℝ)^33
        have hw : |(706270967/1250000000 : ℝ)|=(706270967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4801060133/10000000000 : ℝ)|^41 ≤ (10046749017929/25000000000000 : ℝ)^33
        have hw : |(4801060133/10000000000 : ℝ)|=(4801060133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4776452481/10000000000 : ℝ)*x 0 + (-719368911/10000000000 : ℝ)*x 1 + (3147473529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4776452481/10000000000 : ℝ)^41 ≤ (19965622269607/50000000000000 : ℝ)^33 := by
    have hnat : (4776452481 : ℕ)^41*50000000000000^33 ≤ 19965622269607^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776452481 10000000000 19965622269607 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719368911/10000000000 : ℝ)^41 ≤ (1900286323101/50000000000000 : ℝ)^33 := by
    have hnat : (719368911 : ℕ)^41*50000000000000^33 ≤ 1900286323101^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719368911 10000000000 1900286323101 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3147473529/5000000000 : ℝ)^41 ≤ (11253636559719/20000000000000 : ℝ)^33 := by
    have hnat : (3147473529 : ℕ)^41*20000000000000^33 ≤ 11253636559719^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3147473529 5000000000 11253636559719 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4776452481/10000000000 : ℝ), (-719368911/10000000000 : ℝ), (3147473529/5000000000 : ℝ)] ![(19965622269607/50000000000000 : ℝ), (1900286323101/50000000000000 : ℝ), (11253636559719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4776452481/10000000000 : ℝ)|^41 ≤ (19965622269607/50000000000000 : ℝ)^33
        have hw : |(4776452481/10000000000 : ℝ)|=(4776452481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-719368911/10000000000 : ℝ)|^41 ≤ (1900286323101/50000000000000 : ℝ)^33
        have hw : |(-719368911/10000000000 : ℝ)|=(719368911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3147473529/5000000000 : ℝ)|^41 ≤ (11253636559719/20000000000000 : ℝ)^33
        have hw : |(3147473529/5000000000 : ℝ)|=(3147473529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2378822073/5000000000 : ℝ)*x 0 + (571660923/1000000000 : ℝ)*x 1 + (-1610608663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2378822073/5000000000 : ℝ)^41 ≤ (39735981471371/100000000000000 : ℝ)^33 := by
    have hnat : (2378822073 : ℕ)^41*100000000000000^33 ≤ 39735981471371^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378822073 5000000000 39735981471371 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571660923/1000000000 : ℝ)^41 ≤ (49918668477421/100000000000000 : ℝ)^33 := by
    have hnat : (571660923 : ℕ)^41*100000000000000^33 ≤ 49918668477421^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571660923 1000000000 49918668477421 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1610608663/10000000000 : ℝ)^41 ≤ (161646094319/1562500000000 : ℝ)^33 := by
    have hnat : (1610608663 : ℕ)^41*1562500000000^33 ≤ 161646094319^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610608663 10000000000 161646094319 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2378822073/5000000000 : ℝ), (571660923/1000000000 : ℝ), (-1610608663/10000000000 : ℝ)] ![(39735981471371/100000000000000 : ℝ), (49918668477421/100000000000000 : ℝ), (161646094319/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2378822073/5000000000 : ℝ)|^41 ≤ (39735981471371/100000000000000 : ℝ)^33
        have hw : |(2378822073/5000000000 : ℝ)|=(2378822073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571660923/1000000000 : ℝ)|^41 ≤ (49918668477421/100000000000000 : ℝ)^33
        have hw : |(571660923/1000000000 : ℝ)|=(571660923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1610608663/10000000000 : ℝ)|^41 ≤ (161646094319/1562500000000 : ℝ)^33
        have hw : |(-1610608663/10000000000 : ℝ)|=(1610608663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3169766631/5000000000 : ℝ)*x 0 + (1881259387/5000000000 : ℝ)*x 1 + (500311729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3169766631/5000000000 : ℝ)^41 ≤ (28381881103621/50000000000000 : ℝ)^33 := by
    have hnat : (3169766631 : ℕ)^41*50000000000000^33 ≤ 28381881103621^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169766631 5000000000 28381881103621 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881259387/5000000000 : ℝ)^41 ≤ (29686870306601/100000000000000 : ℝ)^33 := by
    have hnat : (1881259387 : ℕ)^41*100000000000000^33 ≤ 29686870306601^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881259387 5000000000 29686870306601 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500311729/2500000000 : ℝ)^41 ≤ (2709873493503/20000000000000 : ℝ)^33 := by
    have hnat : (500311729 : ℕ)^41*20000000000000^33 ≤ 2709873493503^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500311729 2500000000 2709873493503 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3169766631/5000000000 : ℝ), (1881259387/5000000000 : ℝ), (500311729/2500000000 : ℝ)] ![(28381881103621/50000000000000 : ℝ), (29686870306601/100000000000000 : ℝ), (2709873493503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3169766631/5000000000 : ℝ)|^41 ≤ (28381881103621/50000000000000 : ℝ)^33
        have hw : |(3169766631/5000000000 : ℝ)|=(3169766631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1881259387/5000000000 : ℝ)|^41 ≤ (29686870306601/100000000000000 : ℝ)^33
        have hw : |(1881259387/5000000000 : ℝ)|=(1881259387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500311729/2500000000 : ℝ)|^41 ≤ (2709873493503/20000000000000 : ℝ)^33
        have hw : |(500311729/2500000000 : ℝ)|=(500311729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1242669777/10000000000 : ℝ)*x 0 + (2488870439/5000000000 : ℝ)*x 1 + (5767545751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1242669777/10000000000 : ℝ)^41 ≤ (1873896586287/25000000000000 : ℝ)^33 := by
    have hnat : (1242669777 : ℕ)^41*25000000000000^33 ≤ 1873896586287^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242669777 10000000000 1873896586287 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488870439/5000000000 : ℝ)^41 ≤ (42032533367939/100000000000000 : ℝ)^33 := by
    have hnat : (2488870439 : ℕ)^41*100000000000000^33 ≤ 42032533367939^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488870439 5000000000 42032533367939 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5767545751/10000000000 : ℝ)^41 ≤ (50471880272413/100000000000000 : ℝ)^33 := by
    have hnat : (5767545751 : ℕ)^41*100000000000000^33 ≤ 50471880272413^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5767545751 10000000000 50471880272413 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1242669777/10000000000 : ℝ), (2488870439/5000000000 : ℝ), (5767545751/10000000000 : ℝ)] ![(1873896586287/25000000000000 : ℝ), (42032533367939/100000000000000 : ℝ), (50471880272413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1242669777/10000000000 : ℝ)|^41 ≤ (1873896586287/25000000000000 : ℝ)^33
        have hw : |(-1242669777/10000000000 : ℝ)|=(1242669777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2488870439/5000000000 : ℝ)|^41 ≤ (42032533367939/100000000000000 : ℝ)^33
        have hw : |(2488870439/5000000000 : ℝ)|=(2488870439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5767545751/10000000000 : ℝ)|^41 ≤ (50471880272413/100000000000000 : ℝ)^33
        have hw : |(5767545751/10000000000 : ℝ)|=(5767545751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1155574167/2500000000 : ℝ)*x 0 + (-50828581/10000000000 : ℝ)*x 1 + (3381950411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1155574167/2500000000 : ℝ)^41 ≤ (19168195498799/50000000000000 : ℝ)^33 := by
    have hnat : (1155574167 : ℕ)^41*50000000000000^33 ≤ 19168195498799^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155574167 2500000000 19168195498799 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50828581/10000000000 : ℝ)^41 ≤ (2825159341/2000000000000 : ℝ)^33 := by
    have hnat : (50828581 : ℕ)^41*2000000000000^33 ≤ 2825159341^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50828581 10000000000 2825159341 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3381950411/5000000000 : ℝ)^41 ≤ (3845146939339/6250000000000 : ℝ)^33 := by
    have hnat : (3381950411 : ℕ)^41*6250000000000^33 ≤ 3845146939339^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3381950411 5000000000 3845146939339 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1155574167/2500000000 : ℝ), (-50828581/10000000000 : ℝ), (3381950411/5000000000 : ℝ)] ![(19168195498799/50000000000000 : ℝ), (2825159341/2000000000000 : ℝ), (3845146939339/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1155574167/2500000000 : ℝ)|^41 ≤ (19168195498799/50000000000000 : ℝ)^33
        have hw : |(1155574167/2500000000 : ℝ)|=(1155574167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50828581/10000000000 : ℝ)|^41 ≤ (2825159341/2000000000000 : ℝ)^33
        have hw : |(-50828581/10000000000 : ℝ)|=(50828581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3381950411/5000000000 : ℝ)|^41 ≤ (3845146939339/6250000000000 : ℝ)^33
        have hw : |(3381950411/5000000000 : ℝ)|=(3381950411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (115081919/250000000 : ℝ)*x 0 + (1614384599/2500000000 : ℝ)*x 1 + (-716237919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115081919/250000000 : ℝ)^41 ≤ (3814049983317/10000000000000 : ℝ)^33 := by
    have hnat : (115081919 : ℕ)^41*10000000000000^33 ≤ 3814049983317^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115081919 250000000 3814049983317 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1614384599/2500000000 : ℝ)^41 ≤ (29039734211921/50000000000000 : ℝ)^33 := by
    have hnat : (1614384599 : ℕ)^41*50000000000000^33 ≤ 29039734211921^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614384599 2500000000 29039734211921 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716237919/10000000000 : ℝ)^41 ≤ (756006345947/20000000000000 : ℝ)^33 := by
    have hnat : (716237919 : ℕ)^41*20000000000000^33 ≤ 756006345947^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716237919 10000000000 756006345947 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(115081919/250000000 : ℝ), (1614384599/2500000000 : ℝ), (-716237919/10000000000 : ℝ)] ![(3814049983317/10000000000000 : ℝ), (29039734211921/50000000000000 : ℝ), (756006345947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(115081919/250000000 : ℝ)|^41 ≤ (3814049983317/10000000000000 : ℝ)^33
        have hw : |(115081919/250000000 : ℝ)|=(115081919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1614384599/2500000000 : ℝ)|^41 ≤ (29039734211921/50000000000000 : ℝ)^33
        have hw : |(1614384599/2500000000 : ℝ)|=(1614384599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-716237919/10000000000 : ℝ)|^41 ≤ (756006345947/20000000000000 : ℝ)^33
        have hw : |(-716237919/10000000000 : ℝ)|=(716237919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2580246417/5000000000 : ℝ)*x 0 + (5828435879/10000000000 : ℝ)*x 1 + (44180977/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2580246417/5000000000 : ℝ)^41 ≤ (2197913317351/5000000000000 : ℝ)^33 := by
    have hnat : (2580246417 : ℕ)^41*5000000000000^33 ≤ 2197913317351^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580246417 5000000000 2197913317351 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5828435879/10000000000 : ℝ)^41 ≤ (25567375751229/50000000000000 : ℝ)^33 := by
    have hnat : (5828435879 : ℕ)^41*50000000000000^33 ≤ 25567375751229^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5828435879 10000000000 25567375751229 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44180977/500000000 : ℝ)^41 ≤ (1226745535479/25000000000000 : ℝ)^33 := by
    have hnat : (44180977 : ℕ)^41*25000000000000^33 ≤ 1226745535479^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44180977 500000000 1226745535479 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2580246417/5000000000 : ℝ), (5828435879/10000000000 : ℝ), (44180977/500000000 : ℝ)] ![(2197913317351/5000000000000 : ℝ), (25567375751229/50000000000000 : ℝ), (1226745535479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2580246417/5000000000 : ℝ)|^41 ≤ (2197913317351/5000000000000 : ℝ)^33
        have hw : |(2580246417/5000000000 : ℝ)|=(2580246417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5828435879/10000000000 : ℝ)|^41 ≤ (25567375751229/50000000000000 : ℝ)^33
        have hw : |(5828435879/10000000000 : ℝ)|=(5828435879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44180977/500000000 : ℝ)|^41 ≤ (1226745535479/25000000000000 : ℝ)^33
        have hw : |(44180977/500000000 : ℝ)|=(44180977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-116465681/2000000000 : ℝ)*x 0 + (523593137/1000000000 : ℝ)*x 1 + (1187368091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116465681/2000000000 : ℝ)^41 ≤ (2922905379301/100000000000000 : ℝ)^33 := by
    have hnat : (116465681 : ℕ)^41*100000000000000^33 ≤ 2922905379301^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116465681 2000000000 2922905379301 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523593137/1000000000 : ℝ)^41 ≤ (5594757646287/12500000000000 : ℝ)^33 := by
    have hnat : (523593137 : ℕ)^41*12500000000000^33 ≤ 5594757646287^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523593137 1000000000 5594757646287 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187368091/2000000000 : ℝ)^41 ≤ (204371224349/390625000000 : ℝ)^33 := by
    have hnat : (1187368091 : ℕ)^41*390625000000^33 ≤ 204371224349^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187368091 2000000000 204371224349 390625000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116465681/2000000000 : ℝ), (523593137/1000000000 : ℝ), (1187368091/2000000000 : ℝ)] ![(2922905379301/100000000000000 : ℝ), (5594757646287/12500000000000 : ℝ), (204371224349/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116465681/2000000000 : ℝ)|^41 ≤ (2922905379301/100000000000000 : ℝ)^33
        have hw : |(-116465681/2000000000 : ℝ)|=(116465681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523593137/1000000000 : ℝ)|^41 ≤ (5594757646287/12500000000000 : ℝ)^33
        have hw : |(523593137/1000000000 : ℝ)|=(523593137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1187368091/2000000000 : ℝ)|^41 ≤ (204371224349/390625000000 : ℝ)^33
        have hw : |(1187368091/2000000000 : ℝ)|=(1187368091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4338688437/10000000000 : ℝ)*x 0 + (-502141299/10000000000 : ℝ)*x 1 + (3408917931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338688437/10000000000 : ℝ)^41 ≤ (17718027408709/50000000000000 : ℝ)^33 := by
    have hnat : (4338688437 : ℕ)^41*50000000000000^33 ≤ 17718027408709^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338688437 10000000000 17718027408709 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502141299/10000000000 : ℝ)^41 ≤ (2431502132961/100000000000000 : ℝ)^33 := by
    have hnat : (502141299 : ℕ)^41*100000000000000^33 ≤ 2431502132961^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502141299 10000000000 2431502132961 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3408917931/5000000000 : ℝ)^41 ≤ (1941638844797/3125000000000 : ℝ)^33 := by
    have hnat : (3408917931 : ℕ)^41*3125000000000^33 ≤ 1941638844797^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408917931 5000000000 1941638844797 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338688437/10000000000 : ℝ), (-502141299/10000000000 : ℝ), (3408917931/5000000000 : ℝ)] ![(17718027408709/50000000000000 : ℝ), (2431502132961/100000000000000 : ℝ), (1941638844797/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338688437/10000000000 : ℝ)|^41 ≤ (17718027408709/50000000000000 : ℝ)^33
        have hw : |(4338688437/10000000000 : ℝ)|=(4338688437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-502141299/10000000000 : ℝ)|^41 ≤ (2431502132961/100000000000000 : ℝ)^33
        have hw : |(-502141299/10000000000 : ℝ)|=(502141299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3408917931/5000000000 : ℝ)|^41 ≤ (1941638844797/3125000000000 : ℝ)^33
        have hw : |(3408917931/5000000000 : ℝ)|=(3408917931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1472881769/2500000000 : ℝ)*x 0 + (1060624113/2000000000 : ℝ)*x 1 + (-546943151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472881769/2500000000 : ℝ)^41 ≤ (25911678686911/50000000000000 : ℝ)^33 := by
    have hnat : (1472881769 : ℕ)^41*50000000000000^33 ≤ 25911678686911^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472881769 2500000000 25911678686911 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060624113/2000000000 : ℝ)^41 ≤ (11368188527937/25000000000000 : ℝ)^33 := by
    have hnat : (1060624113 : ℕ)^41*25000000000000^33 ≤ 11368188527937^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060624113 2000000000 11368188527937 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546943151/10000000000 : ℝ)^41 ≤ (2703888504719/100000000000000 : ℝ)^33 := by
    have hnat : (546943151 : ℕ)^41*100000000000000^33 ≤ 2703888504719^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546943151 10000000000 2703888504719 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1472881769/2500000000 : ℝ), (1060624113/2000000000 : ℝ), (-546943151/10000000000 : ℝ)] ![(25911678686911/50000000000000 : ℝ), (11368188527937/25000000000000 : ℝ), (2703888504719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1472881769/2500000000 : ℝ)|^41 ≤ (25911678686911/50000000000000 : ℝ)^33
        have hw : |(1472881769/2500000000 : ℝ)|=(1472881769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060624113/2000000000 : ℝ)|^41 ≤ (11368188527937/25000000000000 : ℝ)^33
        have hw : |(1060624113/2000000000 : ℝ)|=(1060624113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-546943151/10000000000 : ℝ)|^41 ≤ (2703888504719/100000000000000 : ℝ)^33
        have hw : |(-546943151/10000000000 : ℝ)|=(546943151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7719158633/10000000000 : ℝ)*x 0 + (1565020047/5000000000 : ℝ)*x 1 + (91527563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7719158633/10000000000 : ℝ)^41 ≤ (72496025934799/100000000000000 : ℝ)^33 := by
    have hnat : (7719158633 : ℕ)^41*100000000000000^33 ≤ 72496025934799^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7719158633 10000000000 72496025934799 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1565020047/5000000000 : ℝ)^41 ≤ (11809430967007/50000000000000 : ℝ)^33 := by
    have hnat : (1565020047 : ℕ)^41*50000000000000^33 ≤ 11809430967007^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565020047 5000000000 11809430967007 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91527563/1250000000 : ℝ)^41 ≤ (3885112109413/100000000000000 : ℝ)^33 := by
    have hnat : (91527563 : ℕ)^41*100000000000000^33 ≤ 3885112109413^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91527563 1250000000 3885112109413 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7719158633/10000000000 : ℝ), (1565020047/5000000000 : ℝ), (91527563/1250000000 : ℝ)] ![(72496025934799/100000000000000 : ℝ), (11809430967007/50000000000000 : ℝ), (3885112109413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7719158633/10000000000 : ℝ)|^41 ≤ (72496025934799/100000000000000 : ℝ)^33
        have hw : |(7719158633/10000000000 : ℝ)|=(7719158633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1565020047/5000000000 : ℝ)|^41 ≤ (11809430967007/50000000000000 : ℝ)^33
        have hw : |(1565020047/5000000000 : ℝ)|=(1565020047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91527563/1250000000 : ℝ)|^41 ≤ (3885112109413/100000000000000 : ℝ)^33
        have hw : |(91527563/1250000000 : ℝ)|=(91527563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-668024251/10000000000 : ℝ)*x 0 + (3153435529/5000000000 : ℝ)*x 1 + (4795852597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668024251/10000000000 : ℝ)^41 ≤ (866629331401/25000000000000 : ℝ)^33 := by
    have hnat : (668024251 : ℕ)^41*25000000000000^33 ≤ 866629331401^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668024251 10000000000 866629331401 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3153435529/5000000000 : ℝ)^41 ≤ (3525039747867/6250000000000 : ℝ)^33 := by
    have hnat : (3153435529 : ℕ)^41*6250000000000^33 ≤ 3525039747867^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3153435529 5000000000 3525039747867 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795852597/10000000000 : ℝ)^41 ≤ (627075729577/1562500000000 : ℝ)^33 := by
    have hnat : (4795852597 : ℕ)^41*1562500000000^33 ≤ 627075729577^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795852597 10000000000 627075729577 1562500000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-668024251/10000000000 : ℝ), (3153435529/5000000000 : ℝ), (4795852597/10000000000 : ℝ)] ![(866629331401/25000000000000 : ℝ), (3525039747867/6250000000000 : ℝ), (627075729577/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-668024251/10000000000 : ℝ)|^41 ≤ (866629331401/25000000000000 : ℝ)^33
        have hw : |(-668024251/10000000000 : ℝ)|=(668024251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3153435529/5000000000 : ℝ)|^41 ≤ (3525039747867/6250000000000 : ℝ)^33
        have hw : |(3153435529/5000000000 : ℝ)|=(3153435529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795852597/10000000000 : ℝ)|^41 ≤ (627075729577/1562500000000 : ℝ)^33
        have hw : |(4795852597/10000000000 : ℝ)|=(4795852597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1180590971/2000000000 : ℝ)*x 0 + (-533063/100000000 : ℝ)*x 1 + (1105993663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1180590971/2000000000 : ℝ)^41 ≤ (51948277226783/100000000000000 : ℝ)^33 := by
    have hnat : (1180590971 : ℕ)^41*100000000000000^33 ≤ 51948277226783^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180590971 2000000000 51948277226783 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533063/100000000 : ℝ)^41 ≤ (149863043623/100000000000000 : ℝ)^33 := by
    have hnat : (533063 : ℕ)^41*100000000000000^33 ≤ 149863043623^33*100000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533063 100000000 149863043623 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105993663/2000000000 : ℝ)^41 ≤ (2395092985823/5000000000000 : ℝ)^33 := by
    have hnat : (1105993663 : ℕ)^41*5000000000000^33 ≤ 2395092985823^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105993663 2000000000 2395092985823 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1180590971/2000000000 : ℝ), (-533063/100000000 : ℝ), (1105993663/2000000000 : ℝ)] ![(51948277226783/100000000000000 : ℝ), (149863043623/100000000000000 : ℝ), (2395092985823/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1180590971/2000000000 : ℝ)|^41 ≤ (51948277226783/100000000000000 : ℝ)^33
        have hw : |(1180590971/2000000000 : ℝ)|=(1180590971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533063/100000000 : ℝ)|^41 ≤ (149863043623/100000000000000 : ℝ)^33
        have hw : |(-533063/100000000 : ℝ)|=(533063/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105993663/2000000000 : ℝ)|^41 ≤ (2395092985823/5000000000000 : ℝ)^33
        have hw : |(1105993663/2000000000 : ℝ)|=(1105993663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4209835577/10000000000 : ℝ)*x 0 + (1633337457/2500000000 : ℝ)*x 1 + (-1167833049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209835577/10000000000 : ℝ)^41 ≤ (17066634907179/50000000000000 : ℝ)^33 := by
    have hnat : (4209835577 : ℕ)^41*50000000000000^33 ≤ 17066634907179^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209835577 10000000000 17066634907179 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1633337457/2500000000 : ℝ)^41 ≤ (58927820265023/100000000000000 : ℝ)^33 := by
    have hnat : (1633337457 : ℕ)^41*100000000000000^33 ≤ 58927820265023^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633337457 2500000000 58927820265023 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167833049/10000000000 : ℝ)^41 ≤ (1387781982093/20000000000000 : ℝ)^33 := by
    have hnat : (1167833049 : ℕ)^41*20000000000000^33 ≤ 1387781982093^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167833049 10000000000 1387781982093 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209835577/10000000000 : ℝ), (1633337457/2500000000 : ℝ), (-1167833049/10000000000 : ℝ)] ![(17066634907179/50000000000000 : ℝ), (58927820265023/100000000000000 : ℝ), (1387781982093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209835577/10000000000 : ℝ)|^41 ≤ (17066634907179/50000000000000 : ℝ)^33
        have hw : |(4209835577/10000000000 : ℝ)|=(4209835577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1633337457/2500000000 : ℝ)|^41 ≤ (58927820265023/100000000000000 : ℝ)^33
        have hw : |(1633337457/2500000000 : ℝ)|=(1633337457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1167833049/10000000000 : ℝ)|^41 ≤ (1387781982093/20000000000000 : ℝ)^33
        have hw : |(-1167833049/10000000000 : ℝ)|=(1167833049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321055_s1_s1_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3855027339/5000000000 : ℝ)*x 0 + (1089283899/5000000000 : ℝ)*x 1 + (1881989871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3855027339/5000000000 : ℝ)^41 ≤ (14477962368357/20000000000000 : ℝ)^33 := by
    have hnat : (3855027339 : ℕ)^41*20000000000000^33 ≤ 14477962368357^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855027339 5000000000 14477962368357 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089283899/5000000000 : ℝ)^41 ≤ (15056627473579/100000000000000 : ℝ)^33 := by
    have hnat : (1089283899 : ℕ)^41*100000000000000^33 ≤ 15056627473579^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089283899 5000000000 15056627473579 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1881989871/10000000000 : ℝ)^41 ≤ (12553560667807/100000000000000 : ℝ)^33 := by
    have hnat : (1881989871 : ℕ)^41*100000000000000^33 ≤ 12553560667807^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881989871 10000000000 12553560667807 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3855027339/5000000000 : ℝ), (1089283899/5000000000 : ℝ), (1881989871/10000000000 : ℝ)] ![(14477962368357/20000000000000 : ℝ), (15056627473579/100000000000000 : ℝ), (12553560667807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3855027339/5000000000 : ℝ)|^41 ≤ (14477962368357/20000000000000 : ℝ)^33
        have hw : |(3855027339/5000000000 : ℝ)|=(3855027339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089283899/5000000000 : ℝ)|^41 ≤ (15056627473579/100000000000000 : ℝ)^33
        have hw : |(1089283899/5000000000 : ℝ)|=(1089283899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1881989871/10000000000 : ℝ)|^41 ≤ (12553560667807/100000000000000 : ℝ)^33
        have hw : |(1881989871/10000000000 : ℝ)|=(1881989871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321055_s1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((7267/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7267/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3477/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3477/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7073/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7073/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11183/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11183/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(113/250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(113/250 : ℝ)*X 1 2) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s1_pow0 : (7267/10000 : ℝ) ^ (81/16 : ℝ) ≤ (4966500770116581629/25000000000000000000 : ℝ) := by
    have hpowers : (7267/10000 : ℝ)^81 ≤ (4966500770116581629/25000000000000000000 : ℝ)^16 := by
      have hnat : (7267 : ℕ)^81*25000000000000000000^16 ≤ 4966500770116581629^16*10000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7267 10000 4966500770116581629 25000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7267/10000 : ℝ)) (X := (4966500770116581629/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (29966500770116581629/25000000000000000000 : ℝ) ≤ (10364417373601593/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (29966500770116581629/25000000000000000000 : ℝ)^16 ≤ (10364417373601593/10000000000000000 : ℝ)^81 := by
      have hnat : (29966500770116581629 : ℕ)^16*10000000000000000^81 ≤ 10364417373601593^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29966500770116581629 25000000000000000000 10364417373601593 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10364417373601593/10000000000000000 : ℝ)) (X := (29966500770116581629/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (17466500770116581629/12500000000000000000 : ℝ) ≤ (2086558006303/1953125000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (17466500770116581629/12500000000000000000 : ℝ)^16 ≤ (2086558006303/1953125000000 : ℝ)^81 := by
      have hnat : (17466500770116581629 : ℕ)^16*1953125000000^81 ≤ 2086558006303^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17466500770116581629 12500000000000000000 2086558006303 1953125000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2086558006303/1953125000000 : ℝ)) (X := (17466500770116581629/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(28032105661661/559000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7413014387669/169000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (7267/10000 : ℝ)) (alpha := (28032105661661/559000000000000 : ℝ)) (beta := (7413014387669/169000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7267/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(28032105661661/559000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7413014387669/169000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3477/5000 : ℝ) ^ (81/16 : ℝ) ≤ (15896924061078017743/100000000000000000000 : ℝ) := by
    have hpowers : (3477/5000 : ℝ)^81 ≤ (15896924061078017743/100000000000000000000 : ℝ)^16 := by
      have hnat : (3477 : ℕ)^81*100000000000000000000^16 ≤ 15896924061078017743^16*5000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3477 5000 15896924061078017743 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3477/5000 : ℝ)) (X := (15896924061078017743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (115896924061078017743/100000000000000000000 : ℝ) ≤ (10295707118468383/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (115896924061078017743/100000000000000000000 : ℝ)^16 ≤ (10295707118468383/10000000000000000 : ℝ)^81 := by
      have hnat : (115896924061078017743 : ℕ)^16*10000000000000000^81 ≤ 10295707118468383^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115896924061078017743 100000000000000000000 10295707118468383 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10295707118468383/10000000000000000 : ℝ)) (X := (115896924061078017743/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (65896924061078017743/50000000000000000000 : ℝ) ≤ (1320057969450073/1250000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (65896924061078017743/50000000000000000000 : ℝ)^16 ≤ (1320057969450073/1250000000000000 : ℝ)^81 := by
      have hnat : (65896924061078017743 : ℕ)^16*1250000000000000^81 ≤ 1320057969450073^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65896924061078017743 50000000000000000000 1320057969450073 1250000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1320057969450073/1250000000000000 : ℝ)) (X := (65896924061078017743/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(98569039489461/2318000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(264756637132201/6954000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (3477/5000 : ℝ)) (alpha := (98569039489461/2318000000000000 : ℝ)) (beta := (264756637132201/6954000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3477/5000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(98569039489461/2318000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(264756637132201/6954000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7073/10000 : ℝ) ^ (81/16 : ℝ) ≤ (8661408531202133403/50000000000000000000 : ℝ) := by
    have hpowers : (7073/10000 : ℝ)^81 ≤ (8661408531202133403/50000000000000000000 : ℝ)^16 := by
      have hnat : (7073 : ℕ)^81*50000000000000000000^16 ≤ 8661408531202133403^16*10000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7073 10000 8661408531202133403 50000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7073/10000 : ℝ)) (X := (8661408531202133403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (58661408531202133403/50000000000000000000 : ℝ) ≤ (5160302797814479/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (58661408531202133403/50000000000000000000 : ℝ)^16 ≤ (5160302797814479/5000000000000000 : ℝ)^81 := by
      have hnat : (58661408531202133403 : ℕ)^16*5000000000000000^81 ≤ 5160302797814479^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58661408531202133403 50000000000000000000 5160302797814479 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5160302797814479/5000000000000000 : ℝ)) (X := (58661408531202133403/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (33661408531202133403/25000000000000000000 : ℝ) ≤ (10605214621843873/10000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (33661408531202133403/25000000000000000000 : ℝ)^16 ≤ (10605214621843873/10000000000000000 : ℝ)^81 := by
      have hnat : (33661408531202133403 : ℕ)^16*10000000000000000^81 ≤ 10605214621843873^81*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33661408531202133403 25000000000000000000 10605214621843873 10000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10605214621843873/10000000000000000 : ℝ)) (X := (33661408531202133403/25000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(160302797814479/3536500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(56921805242983/1414600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (7073/10000 : ℝ)) (alpha := (160302797814479/3536500000000000 : ℝ)) (beta := (56921805242983/1414600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7073/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(160302797814479/3536500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(56921805242983/1414600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-32884129/200000000 : ℝ)*X 0 0+(706270967/1250000000 : ℝ)*X 0 1+(4801060133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4776452481/10000000000 : ℝ)*X 1 0+(-719368911/10000000000 : ℝ)*X 1 1+(3147473529/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2378822073/5000000000 : ℝ)*X 2 0+(571660923/1000000000 : ℝ)*X 2 1+(-1610608663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3169766631/5000000000 : ℝ)*X 0 0+(1881259387/5000000000 : ℝ)*X 0 1+(500311729/2500000000 : ℝ)*X 0 2+(3169766631/5000000000 : ℝ)*X 1 0+(1881259387/5000000000 : ℝ)*X 1 1+(500311729/2500000000 : ℝ)*X 1 2+(3169766631/5000000000 : ℝ)*X 2 0+(1881259387/5000000000 : ℝ)*X 2 1+(500311729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1242669777/10000000000 : ℝ)*X 0 0+(2488870439/5000000000 : ℝ)*X 0 1+(5767545751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1155574167/2500000000 : ℝ)*X 1 0+(-50828581/10000000000 : ℝ)*X 1 1+(3381950411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((115081919/250000000 : ℝ)*X 2 0+(1614384599/2500000000 : ℝ)*X 2 1+(-716237919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2580246417/5000000000 : ℝ)*X 0 0+(5828435879/10000000000 : ℝ)*X 0 1+(44180977/500000000 : ℝ)*X 0 2+(2580246417/5000000000 : ℝ)*X 1 0+(5828435879/10000000000 : ℝ)*X 1 1+(44180977/500000000 : ℝ)*X 1 2+(2580246417/5000000000 : ℝ)*X 2 0+(5828435879/10000000000 : ℝ)*X 2 1+(44180977/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-116465681/2000000000 : ℝ)*X 0 0+(523593137/1000000000 : ℝ)*X 0 1+(1187368091/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4338688437/10000000000 : ℝ)*X 1 0+(-502141299/10000000000 : ℝ)*X 1 1+(3408917931/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1472881769/2500000000 : ℝ)*X 2 0+(1060624113/2000000000 : ℝ)*X 2 1+(-546943151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7719158633/10000000000 : ℝ)*X 0 0+(1565020047/5000000000 : ℝ)*X 0 1+(91527563/1250000000 : ℝ)*X 0 2+(7719158633/10000000000 : ℝ)*X 1 0+(1565020047/5000000000 : ℝ)*X 1 1+(91527563/1250000000 : ℝ)*X 1 2+(7719158633/10000000000 : ℝ)*X 2 0+(1565020047/5000000000 : ℝ)*X 2 1+(91527563/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-668024251/10000000000 : ℝ)*X 0 0+(3153435529/5000000000 : ℝ)*X 0 1+(4795852597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1180590971/2000000000 : ℝ)*X 1 0+(-533063/100000000 : ℝ)*X 1 1+(1105993663/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4209835577/10000000000 : ℝ)*X 2 0+(1633337457/2500000000 : ℝ)*X 2 1+(-1167833049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3855027339/5000000000 : ℝ)*X 0 0+(1089283899/5000000000 : ℝ)*X 0 1+(1881989871/10000000000 : ℝ)*X 0 2+(3855027339/5000000000 : ℝ)*X 1 0+(1089283899/5000000000 : ℝ)*X 1 1+(1881989871/10000000000 : ℝ)*X 1 2+(3855027339/5000000000 : ℝ)*X 2 0+(1089283899/5000000000 : ℝ)*X 2 1+(1881989871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((44451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19267108397924127228313719/1639521400000000000000000000000 : ℝ) := by norm_num
    linear_combination (7364299/1000000000000 : ℝ)*(base19) + (311998333889/1000000000000 : ℝ)*(base49) + (960102989049/200000000000 : ℝ)*(major_s1_0) + (960102989049/200000000000 : ℝ)*(major_s1_1) + (960102989049/200000000000 : ℝ)*(major_s1_2) + (21622833/1000000000000 : ℝ)*(sp_s1_0) + (6511/7812500000 : ℝ)*(sp_s1_6) + (7079084772901/1000000000000 : ℝ)*(sp_s1_7) + (1769766468083/250000000000 : ℝ)*(sp_s1_8) + (3539498936793/500000000000 : ℝ)*(sp_s1_9) + (2521913801187/1000000000000 : ℝ)*(sp_s1_13) + (7620407/200000000000 : ℝ)*(sp_s1_15) + (4942931/1000000000000 : ℝ)*(sp_s1_21) + (2836627/25000000000 : ℝ)*(sp_s1_23) + (630478658649/250000000000 : ℝ)*(f.failure) + (3539555669333/500000000000 : ℝ)*(f.sum) + (640696236023112673/3279042800000000000000000000000 : ℝ)*base63 + (88693978137099/282920000000000000000000000 : ℝ)*base65 + (224104634903917/463600000000000000000000000 : ℝ)*base67 + (27631046845221/707300000000000000000000000 : ℝ)*base69 + (74543222078041021/395380700000000000000000000000 : ℝ)*base71 + (20026567626379/33800000000000000000000000 : ℝ)*base72 + (65573017706051/463600000000000000000000000 : ℝ)*base74 + (32873883723591/111800000000000000000000000 : ℝ)*base76 + (36939523378963171/78348400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (3681/3125000000000000 : ℝ)*base87 + (3681/3125000000000000 : ℝ)*base89 + (3681/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11183/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11183/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31359071157435277761829283/1822888925000000000000000000000 : ℝ) := by norm_num
    linear_combination (3978523/1000000000000 : ℝ)*(base39) + (206989672849/1000000000000 : ℝ)*(base49) + (269081/200000000000 : ℝ)*(base60) + (4314167403947/1000000000000 : ℝ)*(major_s1_0) + (4314167403947/1000000000000 : ℝ)*(major_s1_1) + (4314167403947/1000000000000 : ℝ)*(major_s1_2) + (1181993/250000000000 : ℝ)*(sp_s1_2) + (8388363/200000000000 : ℝ)*(sp_s1_7) + (15882851/125000000000 : ℝ)*(sp_s1_8) + (6361871541717/1000000000000 : ℝ)*(sp_s1_14) + (1590446605181/250000000000 : ℝ)*(sp_s1_15) + (159047718889/25000000000 : ℝ)*(sp_s1_16) + (566584591083/250000000000 : ℝ)*(sp_s1_20) + (15445141/200000000000 : ℝ)*(sp_s1_27) + (2266415590037/1000000000000 : ℝ)*(f.failure) + (6361913483531/1000000000000 : ℝ)*(f.sum) + (225271896464010639/862906000000000000000000000000 : ℝ)*base62 + (478084175826779/1414600000000000000000000000 : ℝ)*base64 + (287134678818713/366000000000000000000000000 : ℝ)*base66 + (3448689868166087/3536500000000000000000000000 : ℝ)*base68 + (750902872133168043/1976903500000000000000000000000 : ℝ)*base71 + (183709672304757/169000000000000000000000000 : ℝ)*base72 + (81161418576307/122000000000000000000000000 : ℝ)*base74 + (396118491696233/559000000000000000000000000 : ℝ)*base76 + (9235078512471359/61854000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1439/6250000000000000 : ℝ)*base87 + (1439/6250000000000000 : ℝ)*base89 + (1439/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(113/250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(113/250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1842102301790504771389083/123556468750000000000000000000 : ℝ) := by norm_num
    linear_combination (127897372593/1000000000000 : ℝ)*(base7) + (94677626431/1000000000000 : ℝ)*(base40) + (12332351417/62500000000 : ℝ)*(base49) + (2050005670199/500000000000 : ℝ)*(major_s1_0) + (2050005670199/500000000000 : ℝ)*(major_s1_1) + (2050005670199/500000000000 : ℝ)*(major_s1_2) + (2730699/125000000000 : ℝ)*(sp_s1_1) + (18755383/1000000000000 : ℝ)*(sp_s1_2) + (223922327/1000000000000 : ℝ)*(sp_s1_9) + (6698277/1000000000000 : ℝ)*(sp_s1_20) + (1493562706763/250000000000 : ℝ)*(sp_s1_21) + (298711449073/50000000000 : ℝ)*(sp_s1_22) + (2987004074671/500000000000 : ℝ)*(sp_s1_23) + (2281800977543/1000000000000 : ℝ)*(sp_s1_27) + (1076955151613/500000000000 : ℝ)*(f.failure) + (1493562706763/250000000000 : ℝ)*(f.sum) + (1831952411833522997/8197607000000000000000000000000 : ℝ)*base62 + (314520625464977/707300000000000000000000000 : ℝ)*base65 + (1643282222263501/3477000000000000000000000000 : ℝ)*base67 + (173207211781523/884125000000000000000000000 : ℝ)*base69 + (314390412694713931/988451750000000000000000000000 : ℝ)*base71 + (5691070941481/84500000000000000000000000 : ℝ)*base73 + (242493928327439/1159000000000000000000000000 : ℝ)*base75 + (225371001666039/279500000000000000000000000 : ℝ)*base77 + (229688861944696157/587613000000000000000000000000 : ℝ)*base78 + (3889/3125000000000000 : ℝ)*base86 + (3889/3125000000000000 : ℝ)*base88 + (3889/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((7267/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7267/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3477/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3477/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7073/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7073/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44451/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44451/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11183/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11183/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(113/250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(113/250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c321055_s1 p hpa hpb X hX hprev0

#print axioms solution
