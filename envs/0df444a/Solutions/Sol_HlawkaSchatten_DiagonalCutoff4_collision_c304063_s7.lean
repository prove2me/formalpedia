-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304063_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:41.007306+00:00
-- url     : https://prove2.me/submissions/5c59ddd4-3530-4e80-bdc9-07ed463bcc16

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
theorem collision_support_c304063_s7_s7_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-214548849/1250000000 : ℝ)*x 0 + (1088304769/2000000000 : ℝ)*x 1 + (1370341571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214548849/1250000000 : ℝ)^133 ≤ (4910077365113/50000000000000 : ℝ)^101 := by
    have hnat : (214548849 : ℕ)^133*50000000000000^101 ≤ 4910077365113^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214548849 1250000000 4910077365113 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088304769/2000000000 : ℝ)^133 ≤ (5609167931057/12500000000000 : ℝ)^101 := by
    have hnat : (1088304769 : ℕ)^133*12500000000000^101 ≤ 5609167931057^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088304769 2000000000 5609167931057 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370341571/2500000000 : ℝ)^133 ≤ (45306501797967/100000000000000 : ℝ)^101 := by
    have hnat : (1370341571 : ℕ)^133*100000000000000^101 ≤ 45306501797967^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370341571 2500000000 45306501797967 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214548849/1250000000 : ℝ), (1088304769/2000000000 : ℝ), (1370341571/2500000000 : ℝ)] ![(4910077365113/50000000000000 : ℝ), (5609167931057/12500000000000 : ℝ), (45306501797967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214548849/1250000000 : ℝ)|^133 ≤ (4910077365113/50000000000000 : ℝ)^101
        have hw : |(-214548849/1250000000 : ℝ)|=(214548849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088304769/2000000000 : ℝ)|^133 ≤ (5609167931057/12500000000000 : ℝ)^101
        have hw : |(1088304769/2000000000 : ℝ)|=(1088304769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370341571/2500000000 : ℝ)|^133 ≤ (45306501797967/100000000000000 : ℝ)^101
        have hw : |(1370341571/2500000000 : ℝ)|=(1370341571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5442855077/10000000000 : ℝ)*x 0 + (-432089297/2500000000 : ℝ)*x 1 + (2735871573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5442855077/10000000000 : ℝ)^133 ≤ (22443900067067/50000000000000 : ℝ)^101 := by
    have hnat : (5442855077 : ℕ)^133*50000000000000^101 ≤ 22443900067067^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442855077 10000000000 22443900067067 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432089297/2500000000 : ℝ)^133 ≤ (9910410385947/100000000000000 : ℝ)^101 := by
    have hnat : (432089297 : ℕ)^133*100000000000000^101 ≤ 9910410385947^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432089297 2500000000 9910410385947 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735871573/5000000000 : ℝ)^133 ≤ (11300447366103/25000000000000 : ℝ)^101 := by
    have hnat : (2735871573 : ℕ)^133*25000000000000^101 ≤ 11300447366103^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735871573 5000000000 11300447366103 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5442855077/10000000000 : ℝ), (-432089297/2500000000 : ℝ), (2735871573/5000000000 : ℝ)] ![(22443900067067/50000000000000 : ℝ), (9910410385947/100000000000000 : ℝ), (11300447366103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5442855077/10000000000 : ℝ)|^133 ≤ (22443900067067/50000000000000 : ℝ)^101
        have hw : |(5442855077/10000000000 : ℝ)|=(5442855077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432089297/2500000000 : ℝ)|^133 ≤ (9910410385947/100000000000000 : ℝ)^101
        have hw : |(-432089297/2500000000 : ℝ)|=(432089297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735871573/5000000000 : ℝ)|^133 ≤ (11300447366103/25000000000000 : ℝ)^101
        have hw : |(2735871573/5000000000 : ℝ)|=(2735871573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5470671133/10000000000 : ℝ)*x 0 + (2732825499/5000000000 : ℝ)*x 1 + (-33940049/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5470671133/10000000000 : ℝ)^133 ≤ (45190128169871/100000000000000 : ℝ)^101 := by
    have hnat : (5470671133 : ℕ)^133*100000000000000^101 ≤ 45190128169871^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470671133 10000000000 45190128169871 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732825499/5000000000 : ℝ)^133 ≤ (5641941133837/12500000000000 : ℝ)^101 := by
    have hnat : (2732825499 : ℕ)^133*12500000000000^101 ≤ 5641941133837^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732825499 5000000000 5641941133837 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33940049/200000000 : ℝ)^133 ≤ (9674342742369/100000000000000 : ℝ)^101 := by
    have hnat : (33940049 : ℕ)^133*100000000000000^101 ≤ 9674342742369^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33940049 200000000 9674342742369 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5470671133/10000000000 : ℝ), (2732825499/5000000000 : ℝ), (-33940049/200000000 : ℝ)] ![(45190128169871/100000000000000 : ℝ), (5641941133837/12500000000000 : ℝ), (9674342742369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5470671133/10000000000 : ℝ)|^133 ≤ (45190128169871/100000000000000 : ℝ)^101
        have hw : |(5470671133/10000000000 : ℝ)|=(5470671133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732825499/5000000000 : ℝ)|^133 ≤ (5641941133837/12500000000000 : ℝ)^101
        have hw : |(2732825499/5000000000 : ℝ)|=(2732825499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33940049/200000000 : ℝ)|^133 ≤ (9674342742369/100000000000000 : ℝ)^101
        have hw : |(-33940049/200000000 : ℝ)|=(33940049/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4359547871/10000000000 : ℝ)*x 0 + (271747183/625000000 : ℝ)*x 1 + (4318014299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359547871/10000000000 : ℝ)^133 ≤ (6702473021641/20000000000000 : ℝ)^101 := by
    have hnat : (4359547871 : ℕ)^133*20000000000000^101 ≤ 6702473021641^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359547871 10000000000 6702473021641 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271747183/625000000 : ℝ)^133 ≤ (4174382919649/12500000000000 : ℝ)^101 := by
    have hnat : (271747183 : ℕ)^133*12500000000000^101 ≤ 4174382919649^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271747183 625000000 4174382919649 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4318014299/10000000000 : ℝ)^133 ≤ (33092571519437/100000000000000 : ℝ)^101 := by
    have hnat : (4318014299 : ℕ)^133*100000000000000^101 ≤ 33092571519437^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318014299 10000000000 33092571519437 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359547871/10000000000 : ℝ), (271747183/625000000 : ℝ), (4318014299/10000000000 : ℝ)] ![(6702473021641/20000000000000 : ℝ), (4174382919649/12500000000000 : ℝ), (33092571519437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359547871/10000000000 : ℝ)|^133 ≤ (6702473021641/20000000000000 : ℝ)^101
        have hw : |(4359547871/10000000000 : ℝ)|=(4359547871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271747183/625000000 : ℝ)|^133 ≤ (4174382919649/12500000000000 : ℝ)^101
        have hw : |(271747183/625000000 : ℝ)|=(271747183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4318014299/10000000000 : ℝ)|^133 ≤ (33092571519437/100000000000000 : ℝ)^101
        have hw : |(4318014299/10000000000 : ℝ)|=(4318014299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-97793581/625000000 : ℝ)*x 0 + (2279901523/5000000000 : ℝ)*x 1 + (1604177467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97793581/625000000 : ℝ)^133 ≤ (8693613695913/100000000000000 : ℝ)^101 := by
    have hnat : (97793581 : ℕ)^133*100000000000000^101 ≤ 8693613695913^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97793581 625000000 8693613695913 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279901523/5000000000 : ℝ)^133 ≤ (17777038073149/50000000000000 : ℝ)^101 := by
    have hnat : (2279901523 : ℕ)^133*50000000000000^101 ≤ 17777038073149^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279901523 5000000000 17777038073149 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1604177467/2500000000 : ℝ)^133 ≤ (2787615507003/5000000000000 : ℝ)^101 := by
    have hnat : (1604177467 : ℕ)^133*5000000000000^101 ≤ 2787615507003^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604177467 2500000000 2787615507003 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97793581/625000000 : ℝ), (2279901523/5000000000 : ℝ), (1604177467/2500000000 : ℝ)] ![(8693613695913/100000000000000 : ℝ), (17777038073149/50000000000000 : ℝ), (2787615507003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97793581/625000000 : ℝ)|^133 ≤ (8693613695913/100000000000000 : ℝ)^101
        have hw : |(-97793581/625000000 : ℝ)|=(97793581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2279901523/5000000000 : ℝ)|^133 ≤ (17777038073149/50000000000000 : ℝ)^101
        have hw : |(2279901523/5000000000 : ℝ)|=(2279901523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1604177467/2500000000 : ℝ)|^133 ≤ (2787615507003/5000000000000 : ℝ)^101
        have hw : |(1604177467/2500000000 : ℝ)|=(1604177467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5007681383/10000000000 : ℝ)*x 0 + (-890133797/10000000000 : ℝ)*x 1 + (800871759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5007681383/10000000000 : ℝ)^133 ≤ (8044555847673/20000000000000 : ℝ)^101 := by
    have hnat : (5007681383 : ℕ)^133*20000000000000^101 ≤ 8044555847673^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007681383 10000000000 8044555847673 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890133797/10000000000 : ℝ)^133 ≤ (2068137677631/50000000000000 : ℝ)^101 := by
    have hnat : (890133797 : ℕ)^133*50000000000000^101 ≤ 2068137677631^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890133797 10000000000 2068137677631 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800871759/1250000000 : ℝ)^133 ≤ (55640945386017/100000000000000 : ℝ)^101 := by
    have hnat : (800871759 : ℕ)^133*100000000000000^101 ≤ 55640945386017^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800871759 1250000000 55640945386017 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5007681383/10000000000 : ℝ), (-890133797/10000000000 : ℝ), (800871759/1250000000 : ℝ)] ![(8044555847673/20000000000000 : ℝ), (2068137677631/50000000000000 : ℝ), (55640945386017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5007681383/10000000000 : ℝ)|^133 ≤ (8044555847673/20000000000000 : ℝ)^101
        have hw : |(5007681383/10000000000 : ℝ)|=(5007681383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890133797/10000000000 : ℝ)|^133 ≤ (2068137677631/50000000000000 : ℝ)^101
        have hw : |(-890133797/10000000000 : ℝ)|=(890133797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(800871759/1250000000 : ℝ)|^133 ≤ (55640945386017/100000000000000 : ℝ)^101
        have hw : |(800871759/1250000000 : ℝ)|=(800871759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2401439987/5000000000 : ℝ)*x 0 + (1323763101/2000000000 : ℝ)*x 1 + (-843465061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2401439987/5000000000 : ℝ)^133 ≤ (9517686605033/25000000000000 : ℝ)^101 := by
    have hnat : (2401439987 : ℕ)^133*25000000000000^101 ≤ 9517686605033^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401439987 5000000000 9517686605033 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1323763101/2000000000 : ℝ)^133 ≤ (2903807301909/5000000000000 : ℝ)^101 := by
    have hnat : (1323763101 : ℕ)^133*5000000000000^101 ≤ 2903807301909^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323763101 2000000000 2903807301909 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843465061/10000000000 : ℝ)^133 ≤ (3853107522251/100000000000000 : ℝ)^101 := by
    have hnat : (843465061 : ℕ)^133*100000000000000^101 ≤ 3853107522251^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843465061 10000000000 3853107522251 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2401439987/5000000000 : ℝ), (1323763101/2000000000 : ℝ), (-843465061/10000000000 : ℝ)] ![(9517686605033/25000000000000 : ℝ), (2903807301909/5000000000000 : ℝ), (3853107522251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2401439987/5000000000 : ℝ)|^133 ≤ (9517686605033/25000000000000 : ℝ)^101
        have hw : |(2401439987/5000000000 : ℝ)|=(2401439987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1323763101/2000000000 : ℝ)|^133 ≤ (2903807301909/5000000000000 : ℝ)^101
        have hw : |(1323763101/2000000000 : ℝ)|=(1323763101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-843465061/10000000000 : ℝ)|^133 ≤ (3853107522251/100000000000000 : ℝ)^101
        have hw : |(-843465061/10000000000 : ℝ)|=(843465061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4484987291/10000000000 : ℝ)*x 0 + (231732647/400000000 : ℝ)*x 1 + (1271536237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4484987291/10000000000 : ℝ)^133 ≤ (43484867379/125000000000 : ℝ)^101 := by
    have hnat : (4484987291 : ℕ)^133*125000000000^101 ≤ 43484867379^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484987291 10000000000 43484867379 125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231732647/400000000 : ℝ)^133 ≤ (304575582923/625000000000 : ℝ)^101 := by
    have hnat : (231732647 : ℕ)^133*625000000000^101 ≤ 304575582923^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231732647 400000000 304575582923 625000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271536237/5000000000 : ℝ)^133 ≤ (16480012810029/100000000000000 : ℝ)^101 := by
    have hnat : (1271536237 : ℕ)^133*100000000000000^101 ≤ 16480012810029^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271536237 5000000000 16480012810029 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4484987291/10000000000 : ℝ), (231732647/400000000 : ℝ), (1271536237/5000000000 : ℝ)] ![(43484867379/125000000000 : ℝ), (304575582923/625000000000 : ℝ), (16480012810029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4484987291/10000000000 : ℝ)|^133 ≤ (43484867379/125000000000 : ℝ)^101
        have hw : |(4484987291/10000000000 : ℝ)|=(4484987291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231732647/400000000 : ℝ)|^133 ≤ (304575582923/625000000000 : ℝ)^101
        have hw : |(231732647/400000000 : ℝ)|=(231732647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271536237/5000000000 : ℝ)|^133 ≤ (16480012810029/100000000000000 : ℝ)^101
        have hw : |(1271536237/5000000000 : ℝ)|=(1271536237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-8750731/100000000 : ℝ)*x 0 + (1254456751/2500000000 : ℝ)*x 1 + (6405624233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8750731/100000000 : ℝ)^133 ≤ (4044366079307/100000000000000 : ℝ)^101 := by
    have hnat : (8750731 : ℕ)^133*100000000000000^101 ≤ 4044366079307^101*100000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8750731 100000000 4044366079307 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1254456751/2500000000 : ℝ)^133 ≤ (40330124675713/100000000000000 : ℝ)^101 := by
    have hnat : (1254456751 : ℕ)^133*100000000000000^101 ≤ 40330124675713^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254456751 2500000000 40330124675713 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6405624233/10000000000 : ℝ)^133 ≤ (6953188653227/12500000000000 : ℝ)^101 := by
    have hnat : (6405624233 : ℕ)^133*12500000000000^101 ≤ 6953188653227^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6405624233 10000000000 6953188653227 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8750731/100000000 : ℝ), (1254456751/2500000000 : ℝ), (6405624233/10000000000 : ℝ)] ![(4044366079307/100000000000000 : ℝ), (40330124675713/100000000000000 : ℝ), (6953188653227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8750731/100000000 : ℝ)|^133 ≤ (4044366079307/100000000000000 : ℝ)^101
        have hw : |(-8750731/100000000 : ℝ)|=(8750731/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1254456751/2500000000 : ℝ)|^133 ≤ (40330124675713/100000000000000 : ℝ)^101
        have hw : |(1254456751/2500000000 : ℝ)|=(1254456751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6405624233/10000000000 : ℝ)|^133 ≤ (6953188653227/12500000000000 : ℝ)^101
        have hw : |(6405624233/10000000000 : ℝ)|=(6405624233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4583409799/10000000000 : ℝ)*x 0 + (-156408541/1000000000 : ℝ)*x 1 + (639588803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4583409799/10000000000 : ℝ)^133 ≤ (35796661990917/100000000000000 : ℝ)^101 := by
    have hnat : (4583409799 : ℕ)^133*100000000000000^101 ≤ 35796661990917^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583409799 10000000000 35796661990917 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156408541/1000000000 : ℝ)^133 ≤ (8689137141349/100000000000000 : ℝ)^101 := by
    have hnat : (156408541 : ℕ)^133*100000000000000^101 ≤ 8689137141349^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156408541 1000000000 8689137141349 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639588803/1000000000 : ℝ)^133 ≤ (55514200859383/100000000000000 : ℝ)^101 := by
    have hnat : (639588803 : ℕ)^133*100000000000000^101 ≤ 55514200859383^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639588803 1000000000 55514200859383 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4583409799/10000000000 : ℝ), (-156408541/1000000000 : ℝ), (639588803/1000000000 : ℝ)] ![(35796661990917/100000000000000 : ℝ), (8689137141349/100000000000000 : ℝ), (55514200859383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4583409799/10000000000 : ℝ)|^133 ≤ (35796661990917/100000000000000 : ℝ)^101
        have hw : |(4583409799/10000000000 : ℝ)|=(4583409799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156408541/1000000000 : ℝ)|^133 ≤ (8689137141349/100000000000000 : ℝ)^101
        have hw : |(-156408541/1000000000 : ℝ)|=(156408541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639588803/1000000000 : ℝ)|^133 ≤ (55514200859383/100000000000000 : ℝ)^101
        have hw : |(639588803/1000000000 : ℝ)|=(639588803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6393899153/10000000000 : ℝ)*x 0 + (504223/1000000 : ℝ)*x 1 + (-34182007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6393899153/10000000000 : ℝ)^133 ≤ (55491469781133/100000000000000 : ℝ)^101 := by
    have hnat : (6393899153 : ℕ)^133*100000000000000^101 ≤ 55491469781133^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6393899153 10000000000 55491469781133 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504223/1000000 : ℝ)^133 ≤ (10147150341763/25000000000000 : ℝ)^101 := by
    have hnat : (504223 : ℕ)^133*25000000000000^101 ≤ 10147150341763^101*1000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504223 1000000 10147150341763 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34182007/400000000 : ℝ)^133 ≤ (3919928837337/100000000000000 : ℝ)^101 := by
    have hnat : (34182007 : ℕ)^133*100000000000000^101 ≤ 3919928837337^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34182007 400000000 3919928837337 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6393899153/10000000000 : ℝ), (504223/1000000 : ℝ), (-34182007/400000000 : ℝ)] ![(55491469781133/100000000000000 : ℝ), (10147150341763/25000000000000 : ℝ), (3919928837337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6393899153/10000000000 : ℝ)|^133 ≤ (55491469781133/100000000000000 : ℝ)^101
        have hw : |(6393899153/10000000000 : ℝ)|=(6393899153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504223/1000000 : ℝ)|^133 ≤ (10147150341763/25000000000000 : ℝ)^101
        have hw : |(504223/1000000 : ℝ)|=(504223/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34182007/400000000 : ℝ)|^133 ≤ (3919928837337/100000000000000 : ℝ)^101
        have hw : |(-34182007/400000000 : ℝ)|=(34182007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1246659301/2000000000 : ℝ)*x 0 + (1986927643/5000000000 : ℝ)*x 1 + (2565613519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1246659301/2000000000 : ℝ)^133 ≤ (26831680924981/50000000000000 : ℝ)^101 := by
    have hnat : (1246659301 : ℕ)^133*50000000000000^101 ≤ 26831680924981^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246659301 2000000000 26831680924981 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986927643/5000000000 : ℝ)^133 ≤ (29664000924717/100000000000000 : ℝ)^101 := by
    have hnat : (1986927643 : ℕ)^133*100000000000000^101 ≤ 29664000924717^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986927643 5000000000 29664000924717 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565613519/10000000000 : ℝ)^133 ≤ (4168159300831/25000000000000 : ℝ)^101 := by
    have hnat : (2565613519 : ℕ)^133*25000000000000^101 ≤ 4168159300831^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565613519 10000000000 4168159300831 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1246659301/2000000000 : ℝ), (1986927643/5000000000 : ℝ), (2565613519/10000000000 : ℝ)] ![(26831680924981/50000000000000 : ℝ), (29664000924717/100000000000000 : ℝ), (4168159300831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1246659301/2000000000 : ℝ)|^133 ≤ (26831680924981/50000000000000 : ℝ)^101
        have hw : |(1246659301/2000000000 : ℝ)|=(1246659301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1986927643/5000000000 : ℝ)|^133 ≤ (29664000924717/100000000000000 : ℝ)^101
        have hw : |(1986927643/5000000000 : ℝ)|=(1986927643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565613519/10000000000 : ℝ)|^133 ≤ (4168159300831/25000000000000 : ℝ)^101
        have hw : |(2565613519/10000000000 : ℝ)|=(2565613519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-81711601/1000000000 : ℝ)*x 0 + (6018023271/10000000000 : ℝ)*x 1 + (5459467071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81711601/1000000000 : ℝ)^133 ≤ (3695393920511/100000000000000 : ℝ)^101 := by
    have hnat : (81711601 : ℕ)^133*100000000000000^101 ≤ 3695393920511^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81711601 1000000000 3695393920511 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6018023271/10000000000 : ℝ)^133 ≤ (51236311682213/100000000000000 : ℝ)^101 := by
    have hnat : (6018023271 : ℕ)^133*100000000000000^101 ≤ 51236311682213^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6018023271 10000000000 51236311682213 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459467071/10000000000 : ℝ)^133 ≤ (9013658876521/20000000000000 : ℝ)^101 := by
    have hnat : (5459467071 : ℕ)^133*20000000000000^101 ≤ 9013658876521^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459467071 10000000000 9013658876521 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81711601/1000000000 : ℝ), (6018023271/10000000000 : ℝ), (5459467071/10000000000 : ℝ)] ![(3695393920511/100000000000000 : ℝ), (51236311682213/100000000000000 : ℝ), (9013658876521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81711601/1000000000 : ℝ)|^133 ≤ (3695393920511/100000000000000 : ℝ)^101
        have hw : |(-81711601/1000000000 : ℝ)|=(81711601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6018023271/10000000000 : ℝ)|^133 ≤ (51236311682213/100000000000000 : ℝ)^101
        have hw : |(6018023271/10000000000 : ℝ)|=(6018023271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459467071/10000000000 : ℝ)|^133 ≤ (9013658876521/20000000000000 : ℝ)^101
        have hw : |(5459467071/10000000000 : ℝ)|=(5459467071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6423712763/10000000000 : ℝ)*x 0 + (-407909381/5000000000 : ℝ)*x 1 + (5031970331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6423712763/10000000000 : ℝ)^133 ≤ (55832447200027/100000000000000 : ℝ)^101 := by
    have hnat : (6423712763 : ℕ)^133*100000000000000^101 ≤ 55832447200027^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6423712763 10000000000 55832447200027 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407909381/5000000000 : ℝ)^133 ≤ (3687670298371/100000000000000 : ℝ)^101 := by
    have hnat : (407909381 : ℕ)^133*100000000000000^101 ≤ 3687670298371^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407909381 5000000000 3687670298371 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5031970331/10000000000 : ℝ)^133 ≤ (40479882485793/100000000000000 : ℝ)^101 := by
    have hnat : (5031970331 : ℕ)^133*100000000000000^101 ≤ 40479882485793^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031970331 10000000000 40479882485793 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6423712763/10000000000 : ℝ), (-407909381/5000000000 : ℝ), (5031970331/10000000000 : ℝ)] ![(55832447200027/100000000000000 : ℝ), (3687670298371/100000000000000 : ℝ), (40479882485793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6423712763/10000000000 : ℝ)|^133 ≤ (55832447200027/100000000000000 : ℝ)^101
        have hw : |(6423712763/10000000000 : ℝ)|=(6423712763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407909381/5000000000 : ℝ)|^133 ≤ (3687670298371/100000000000000 : ℝ)^101
        have hw : |(-407909381/5000000000 : ℝ)|=(407909381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5031970331/10000000000 : ℝ)|^133 ≤ (40479882485793/100000000000000 : ℝ)^101
        have hw : |(5031970331/10000000000 : ℝ)|=(5031970331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4534931909/10000000000 : ℝ)*x 0 + (1615046397/2500000000 : ℝ)*x 1 + (-153139771/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4534931909/10000000000 : ℝ)^133 ≤ (17649463731691/50000000000000 : ℝ)^101 := by
    have hnat : (4534931909 : ℕ)^133*50000000000000^101 ≤ 17649463731691^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534931909 10000000000 17649463731691 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1615046397/2500000000 : ℝ)^133 ≤ (56250268111669/100000000000000 : ℝ)^101 := by
    have hnat : (1615046397 : ℕ)^133*100000000000000^101 ≤ 56250268111669^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615046397 2500000000 56250268111669 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153139771/1000000000 : ℝ)^133 ≤ (8450804416751/100000000000000 : ℝ)^101 := by
    have hnat : (153139771 : ℕ)^133*100000000000000^101 ≤ 8450804416751^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153139771 1000000000 8450804416751 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4534931909/10000000000 : ℝ), (1615046397/2500000000 : ℝ), (-153139771/1000000000 : ℝ)] ![(17649463731691/50000000000000 : ℝ), (56250268111669/100000000000000 : ℝ), (8450804416751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4534931909/10000000000 : ℝ)|^133 ≤ (17649463731691/50000000000000 : ℝ)^101
        have hw : |(4534931909/10000000000 : ℝ)|=(4534931909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1615046397/2500000000 : ℝ)|^133 ≤ (56250268111669/100000000000000 : ℝ)^101
        have hw : |(1615046397/2500000000 : ℝ)|=(1615046397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153139771/1000000000 : ℝ)|^133 ≤ (8450804416751/100000000000000 : ℝ)^101
        have hw : |(-153139771/1000000000 : ℝ)|=(153139771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304063_s7_s7_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (399318673/625000000 : ℝ)*x 0 + (825447729/2500000000 : ℝ)*x 1 + (123698051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399318673/625000000 : ℝ)^133 ≤ (27718307460099/50000000000000 : ℝ)^101 := by
    have hnat : (399318673 : ℕ)^133*50000000000000^101 ≤ 27718307460099^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399318673 625000000 27718307460099 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825447729/2500000000 : ℝ)^133 ≤ (23242036777509/100000000000000 : ℝ)^101 := by
    have hnat : (825447729 : ℕ)^133*100000000000000^101 ≤ 23242036777509^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825447729 2500000000 23242036777509 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123698051/400000000 : ℝ)^133 ≤ (10660674145399/50000000000000 : ℝ)^101 := by
    have hnat : (123698051 : ℕ)^133*50000000000000^101 ≤ 10660674145399^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123698051 400000000 10660674145399 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399318673/625000000 : ℝ), (825447729/2500000000 : ℝ), (123698051/400000000 : ℝ)] ![(27718307460099/50000000000000 : ℝ), (23242036777509/100000000000000 : ℝ), (10660674145399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399318673/625000000 : ℝ)|^133 ≤ (27718307460099/50000000000000 : ℝ)^101
        have hw : |(399318673/625000000 : ℝ)|=(399318673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825447729/2500000000 : ℝ)|^133 ≤ (23242036777509/100000000000000 : ℝ)^101
        have hw : |(825447729/2500000000 : ℝ)|=(825447729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123698051/400000000 : ℝ)|^133 ≤ (10660674145399/50000000000000 : ℝ)^101
        have hw : |(123698051/400000000 : ℝ)|=(123698051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304063_s7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((3147/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3147/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64/125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64/125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12231/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12231/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18551/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18551/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18787/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18787/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35843/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35843/100000 : ℝ)*X 1 2) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (3147/6250 : ℝ) ^ (33/8 : ℝ) ≤ (2949775725052532907/50000000000000000000 : ℝ) := by
    have hpowers : (3147/6250 : ℝ)^33 ≤ (2949775725052532907/50000000000000000000 : ℝ)^8 := by
      have hnat : (3147 : ℕ)^33*50000000000000000000^8 ≤ 2949775725052532907^8*6250^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3147 6250 2949775725052532907 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3147/6250 : ℝ)) (X := (2949775725052532907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner0a : (52949775725052532907/50000000000000000000 : ℝ) ≤ (5069964783213503/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (52949775725052532907/50000000000000000000 : ℝ)^8 ≤ (5069964783213503/5000000000000000 : ℝ)^33 := by
      have hnat : (52949775725052532907 : ℕ)^8*5000000000000000^33 ≤ 5069964783213503^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52949775725052532907 50000000000000000000 5069964783213503 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5069964783213503/5000000000000000 : ℝ)) (X := (52949775725052532907/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner0b : (27949775725052532907/25000000000000000000 : ℝ) ≤ (2054814484257457/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (27949775725052532907/25000000000000000000 : ℝ)^8 ≤ (2054814484257457/2000000000000000 : ℝ)^33 := by
      have hnat : (27949775725052532907 : ℕ)^8*2000000000000000^33 ≤ 2054814484257457^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27949775725052532907 25000000000000000000 2054814484257457 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2054814484257457/2000000000000000 : ℝ)) (X := (27949775725052532907/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(23321594404501/839200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(134142854860279/5035200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (3147/6250 : ℝ)) (alpha := (23321594404501/839200000000000 : ℝ)) (beta := (134142854860279/5035200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3147/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(23321594404501/839200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(134142854860279/5035200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (64/125 : ℝ) ^ (33/8 : ℝ) ≤ (1580078259837348983/25000000000000000000 : ℝ) := by
    have hpowers : (64/125 : ℝ)^33 ≤ (1580078259837348983/25000000000000000000 : ℝ)^8 := by
      have hnat : (64 : ℕ)^33*25000000000000000000^8 ≤ 1580078259837348983^8*125^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64 125 1580078259837348983 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64/125 : ℝ)) (X := (1580078259837348983/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner1a : (26580078259837348983/25000000000000000000 : ℝ) ≤ (5074840858109289/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (26580078259837348983/25000000000000000000 : ℝ)^8 ≤ (5074840858109289/5000000000000000 : ℝ)^33 := by
      have hnat : (26580078259837348983 : ℕ)^8*5000000000000000^33 ≤ 5074840858109289^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26580078259837348983 25000000000000000000 5074840858109289 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5074840858109289/5000000000000000 : ℝ)) (X := (26580078259837348983/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner1b : (14080078259837348983/12500000000000000000 : ℝ) ≤ (10292766835593847/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (14080078259837348983/12500000000000000000 : ℝ)^8 ≤ (10292766835593847/10000000000000000 : ℝ)^33 := by
      have hnat : (14080078259837348983 : ℕ)^8*10000000000000000^33 ≤ 10292766835593847^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14080078259837348983 12500000000000000000 10292766835593847 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10292766835593847/10000000000000000 : ℝ)) (X := (14080078259837348983/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(74840858109289/2560000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(143085119375269/5120000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (64/125 : ℝ)) (alpha := (74840858109289/2560000000000000 : ℝ)) (beta := (143085119375269/5120000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (64/125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(74840858109289/2560000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(143085119375269/5120000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (12231/25000 : ℝ) ^ (33/8 : ℝ) ≤ (2619679001959298371/50000000000000000000 : ℝ) := by
    have hpowers : (12231/25000 : ℝ)^33 ≤ (2619679001959298371/50000000000000000000 : ℝ)^8 := by
      have hnat : (12231 : ℕ)^33*50000000000000000000^8 ≤ 2619679001959298371^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12231 25000 2619679001959298371 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12231/25000 : ℝ)) (X := (2619679001959298371/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner2a : (52619679001959298371/50000000000000000000 : ℝ) ≤ (10124568683859437/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (52619679001959298371/50000000000000000000 : ℝ)^8 ≤ (10124568683859437/10000000000000000 : ℝ)^33 := by
      have hnat : (52619679001959298371 : ℕ)^8*10000000000000000^33 ≤ 10124568683859437^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52619679001959298371 50000000000000000000 10124568683859437 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10124568683859437/10000000000000000 : ℝ)) (X := (52619679001959298371/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s7_corner2b : (27619679001959298371/25000000000000000000 : ℝ) ≤ (10244524047551897/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (27619679001959298371/25000000000000000000 : ℝ)^8 ≤ (10244524047551897/10000000000000000 : ℝ)^33 := by
      have hnat : (27619679001959298371 : ℕ)^8*10000000000000000^33 ≤ 10244524047551897^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27619679001959298371 25000000000000000000 10244524047551897 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10244524047551897/10000000000000000 : ℝ)) (X := (27619679001959298371/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(124568683859437/4892400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1999256061541/81540000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (12231/25000 : ℝ)) (alpha := (124568683859437/4892400000000000 : ℝ)) (beta := (1999256061541/81540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12231/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(124568683859437/4892400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1999256061541/81540000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-214548849/1250000000 : ℝ)*X 0 0+(1088304769/2000000000 : ℝ)*X 0 1+(1370341571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((5442855077/10000000000 : ℝ)*X 1 0+(-432089297/2500000000 : ℝ)*X 1 1+(2735871573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((5470671133/10000000000 : ℝ)*X 2 0+(2732825499/5000000000 : ℝ)*X 2 1+(-33940049/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((4359547871/10000000000 : ℝ)*X 0 0+(271747183/625000000 : ℝ)*X 0 1+(4318014299/10000000000 : ℝ)*X 0 2+(4359547871/10000000000 : ℝ)*X 1 0+(271747183/625000000 : ℝ)*X 1 1+(4318014299/10000000000 : ℝ)*X 1 2+(4359547871/10000000000 : ℝ)*X 2 0+(271747183/625000000 : ℝ)*X 2 1+(4318014299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-97793581/625000000 : ℝ)*X 0 0+(2279901523/5000000000 : ℝ)*X 0 1+(1604177467/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((5007681383/10000000000 : ℝ)*X 1 0+(-890133797/10000000000 : ℝ)*X 1 1+(800871759/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((2401439987/5000000000 : ℝ)*X 2 0+(1323763101/2000000000 : ℝ)*X 2 1+(-843465061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((4484987291/10000000000 : ℝ)*X 0 0+(231732647/400000000 : ℝ)*X 0 1+(1271536237/5000000000 : ℝ)*X 0 2+(4484987291/10000000000 : ℝ)*X 1 0+(231732647/400000000 : ℝ)*X 1 1+(1271536237/5000000000 : ℝ)*X 1 2+(4484987291/10000000000 : ℝ)*X 2 0+(231732647/400000000 : ℝ)*X 2 1+(1271536237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-8750731/100000000 : ℝ)*X 0 0+(1254456751/2500000000 : ℝ)*X 0 1+(6405624233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((4583409799/10000000000 : ℝ)*X 1 0+(-156408541/1000000000 : ℝ)*X 1 1+(639588803/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((6393899153/10000000000 : ℝ)*X 2 0+(504223/1000000 : ℝ)*X 2 1+(-34182007/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((1246659301/2000000000 : ℝ)*X 0 0+(1986927643/5000000000 : ℝ)*X 0 1+(2565613519/10000000000 : ℝ)*X 0 2+(1246659301/2000000000 : ℝ)*X 1 0+(1986927643/5000000000 : ℝ)*X 1 1+(2565613519/10000000000 : ℝ)*X 1 2+(1246659301/2000000000 : ℝ)*X 2 0+(1986927643/5000000000 : ℝ)*X 2 1+(2565613519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-81711601/1000000000 : ℝ)*X 0 0+(6018023271/10000000000 : ℝ)*X 0 1+(5459467071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((6423712763/10000000000 : ℝ)*X 1 0+(-407909381/5000000000 : ℝ)*X 1 1+(5031970331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((4534931909/10000000000 : ℝ)*X 2 0+(1615046397/2500000000 : ℝ)*X 2 1+(-153139771/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((399318673/625000000 : ℝ)*X 0 0+(825447729/2500000000 : ℝ)*X 0 1+(123698051/400000000 : ℝ)*X 0 2+(399318673/625000000 : ℝ)*X 1 0+(825447729/2500000000 : ℝ)*X 1 1+(123698051/400000000 : ℝ)*X 1 2+(399318673/625000000 : ℝ)*X 2 0+(825447729/2500000000 : ℝ)*X 2 1+(123698051/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304063_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((18551/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18551/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (790860346679780042245710613/243300864000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145831/250000000000 : ℝ)*(base50) + (32323542229/250000000000 : ℝ)*(base60) + (828000183873/200000000000 : ℝ)*(major_s7_0) + (828000183873/200000000000 : ℝ)*(major_s7_1) + (828000183873/200000000000 : ℝ)*(major_s7_2) + (4874947/1000000000000 : ℝ)*(sp_s7_0) + (46931/12500000000 : ℝ)*(sp_s7_6) + (2775205577677/500000000000 : ℝ)*(sp_s7_7) + (2775203325829/500000000000 : ℝ)*(sp_s7_8) + (5550406627181/1000000000000 : ℝ)*(sp_s7_9) + (341196399539/125000000000 : ℝ)*(sp_s7_13) + (244353/25000000000 : ℝ)*(sp_s7_14) + (19152763/1000000000000 : ℝ)*(sp_s7_15) + (479431/25000000000 : ℝ)*(sp_s7_23) + (341196868849/125000000000 : ℝ)*(f.failure) + (5550425804421/1000000000000 : ℝ)*(f.sum) + (167645572961758069/2087424000000000000000000000000 : ℝ)*base63 + (5572978655513/27180000000000000000000000 : ℝ)*base65 + (295631059374363/1024000000000000000000000000 : ℝ)*base66 + (67297767745001/326160000000000000000000000 : ℝ)*base68 + (37043044600726163/228094560000000000000000000000 : ℝ)*base71 + (9848470351357/335680000000000000000000000 : ℝ)*base73 + (177313794205097/512000000000000000000000000 : ℝ)*base75 + (13309925841413/167840000000000000000000000 : ℝ)*base77 + (475447067075972387/1074176000000000000000000000000 : ℝ)*base78 + (757/3125000000000000 : ℝ)*base87 + (757/3125000000000000 : ℝ)*base89 + (757/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18787/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18787/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (87743599201782914372088517039/10948538880000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2746819/1000000000000 : ℝ)*(base60) + (4184885366777/1000000000000 : ℝ)*(major_s7_0) + (4184885366777/1000000000000 : ℝ)*(major_s7_1) + (4184885366777/1000000000000 : ℝ)*(major_s7_2) + (3905457/250000000000 : ℝ)*(sp_s7_0) + (7316379/500000000000 : ℝ)*(sp_s7_1) + (11027733/250000000000 : ℝ)*(sp_s7_2) + (5871277/250000000000 : ℝ)*(sp_s7_7) + (19872673/1000000000000 : ℝ)*(sp_s7_8) + (701320112989/125000000000 : ℝ)*(sp_s7_14) + (2805282752709/500000000000 : ℝ)*(sp_s7_15) + (5610555899917/1000000000000 : ℝ)*(sp_s7_16) + (2759102113563/1000000000000 : ℝ)*(sp_s7_20) + (65937743/1000000000000 : ℝ)*(sp_s7_27) + (1379584025653/500000000000 : ℝ)*(f.failure) + (5610600010849/1000000000000 : ℝ)*(f.sum) + (8193261877836178343/31311360000000000000000000000000 : ℝ)*base63 + (20637814069529/81540000000000000000000000 : ℝ)*base65 + (3691842436070013/5120000000000000000000000000 : ℝ)*base67 + (2762036067699509/4892400000000000000000000000 : ℝ)*base69 + (1393291537621567391/3421418400000000000000000000000 : ℝ)*base70 + (741614416136063/5035200000000000000000000000 : ℝ)*base73 + (362893801515553/2560000000000000000000000000 : ℝ)*base75 + (140969894874637/839200000000000000000000000 : ℝ)*base77 + (488839950186324511/16112640000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1023/6250000000000000 : ℝ)*base86 + (1023/6250000000000000 : ℝ)*base88 + (1023/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35843/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35843/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (46981978195709142423398263397/5474269440000000000000000000000000 : ℝ) := by norm_num
    linear_combination (197687/31250000000 : ℝ)*(base15) + (217935135977/1000000000000 : ℝ)*(base40) + (1945543952429/500000000000 : ℝ)*(major_s7_0) + (1945543952429/500000000000 : ℝ)*(major_s7_1) + (1945543952429/500000000000 : ℝ)*(major_s7_2) + (44059371/1000000000000 : ℝ)*(sp_s7_0) + (41181613/1000000000000 : ℝ)*(sp_s7_1) + (1187373/100000000000 : ℝ)*(sp_s7_2) + (24788723/1000000000000 : ℝ)*(sp_s7_9) + (63813961/1000000000000 : ℝ)*(sp_s7_20) + (2608333319439/500000000000 : ℝ)*(sp_s7_21) + (1304165797663/250000000000 : ℝ)*(sp_s7_22) + (1043334807159/200000000000 : ℝ)*(sp_s7_23) + (641349609181/250000000000 : ℝ)*(sp_s7_27) + (513092450137/200000000000 : ℝ)*(f.failure) + (5216710698249/1000000000000 : ℝ)*(f.sum) + (2869966491969202189/15655680000000000000000000000000 : ℝ)*base62 + (14573324880281/20385000000000000000000000 : ℝ)*base64 + (1808808528537599/2560000000000000000000000000 : ℝ)*base66 + (1676607609562207/2446200000000000000000000000 : ℝ)*base68 + (334613169500989067/1710709200000000000000000000000 : ℝ)*base70 + (1896633445199749/2517600000000000000000000000 : ℝ)*base72 + (384935129339019/1280000000000000000000000000 : ℝ)*base74 + (106942538521271/419600000000000000000000000 : ℝ)*base76 + (901877105463052853/8056320000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2383/2500000000000000 : ℝ)*base87 + (2383/2500000000000000 : ℝ)*base89 + (2383/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((3147/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3147/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64/125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64/125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12231/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12231/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18551/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18551/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18787/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18787/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35843/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35843/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304063_s7 p hpa hpb X hX hprev6

#print axioms solution
