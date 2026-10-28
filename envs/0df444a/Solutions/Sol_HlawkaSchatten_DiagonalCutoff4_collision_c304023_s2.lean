-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304023_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:37:32.068491+00:00
-- url     : https://prove2.me/submissions/60c50a88-64a1-4ccf-9f40-3886f9e1aab2

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
theorem collision_support_c304023_s2_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3032784783/10000000000 : ℝ)*x 0 + (1556163689/2500000000 : ℝ)*x 1 + (-139384151/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3032784783/10000000000 : ℝ)^17 ≤ (1313071132197/6250000000000 : ℝ)^13 := by
    have hnat : (3032784783 : ℕ)^17*6250000000000^13 ≤ 1313071132197^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3032784783 10000000000 1313071132197 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1556163689/2500000000 : ℝ)^17 ≤ (13449499692649/25000000000000 : ℝ)^13 := by
    have hnat : (1556163689 : ℕ)^17*25000000000000^13 ≤ 13449499692649^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556163689 2500000000 13449499692649 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139384151/400000000 : ℝ)^17 ≤ (1259643155063/5000000000000 : ℝ)^13 := by
    have hnat : (139384151 : ℕ)^17*5000000000000^13 ≤ 1259643155063^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139384151 400000000 1259643155063 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3032784783/10000000000 : ℝ), (1556163689/2500000000 : ℝ), (-139384151/400000000 : ℝ)] ![(1313071132197/6250000000000 : ℝ), (13449499692649/25000000000000 : ℝ), (1259643155063/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3032784783/10000000000 : ℝ)|^17 ≤ (1313071132197/6250000000000 : ℝ)^13
        have hw : |(3032784783/10000000000 : ℝ)|=(3032784783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1556163689/2500000000 : ℝ)|^17 ≤ (13449499692649/25000000000000 : ℝ)^13
        have hw : |(1556163689/2500000000 : ℝ)|=(1556163689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139384151/400000000 : ℝ)|^17 ≤ (1259643155063/5000000000000 : ℝ)^13
        have hw : |(-139384151/400000000 : ℝ)|=(139384151/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (853259239/2000000000 : ℝ)*x 0 + (76365687/156250000 : ℝ)*x 1 + (150957533/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853259239/2000000000 : ℝ)^17 ≤ (32826194878849/100000000000000 : ℝ)^13 := by
    have hnat : (853259239 : ℕ)^17*100000000000000^13 ≤ 32826194878849^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853259239 2000000000 32826194878849 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76365687/156250000 : ℝ)^17 ≤ (1960559408221/5000000000000 : ℝ)^13 := by
    have hnat : (76365687 : ℕ)^17*5000000000000^13 ≤ 1960559408221^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76365687 156250000 1960559408221 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150957533/400000000 : ℝ)^17 ≤ (6990654236381/25000000000000 : ℝ)^13 := by
    have hnat : (150957533 : ℕ)^17*25000000000000^13 ≤ 6990654236381^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150957533 400000000 6990654236381 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853259239/2000000000 : ℝ), (76365687/156250000 : ℝ), (150957533/400000000 : ℝ)] ![(32826194878849/100000000000000 : ℝ), (1960559408221/5000000000000 : ℝ), (6990654236381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853259239/2000000000 : ℝ)|^17 ≤ (32826194878849/100000000000000 : ℝ)^13
        have hw : |(853259239/2000000000 : ℝ)|=(853259239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76365687/156250000 : ℝ)|^17 ≤ (1960559408221/5000000000000 : ℝ)^13
        have hw : |(76365687/156250000 : ℝ)|=(76365687/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150957533/400000000 : ℝ)|^17 ≤ (6990654236381/25000000000000 : ℝ)^13
        have hw : |(150957533/400000000 : ℝ)|=(150957533/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1672338861/5000000000 : ℝ)*x 0 + (2393775437/5000000000 : ℝ)*x 1 + (2383601653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1672338861/5000000000 : ℝ)^17 ≤ (23878208907147/100000000000000 : ℝ)^13 := by
    have hnat : (1672338861 : ℕ)^17*100000000000000^13 ≤ 23878208907147^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672338861 5000000000 23878208907147 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2393775437/5000000000 : ℝ)^17 ≤ (19083444260011/50000000000000 : ℝ)^13 := by
    have hnat : (2393775437 : ℕ)^17*50000000000000^13 ≤ 19083444260011^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393775437 5000000000 19083444260011 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383601653/5000000000 : ℝ)^17 ≤ (1518196102531/4000000000000 : ℝ)^13 := by
    have hnat : (2383601653 : ℕ)^17*4000000000000^13 ≤ 1518196102531^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383601653 5000000000 1518196102531 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1672338861/5000000000 : ℝ), (2393775437/5000000000 : ℝ), (2383601653/5000000000 : ℝ)] ![(23878208907147/100000000000000 : ℝ), (19083444260011/50000000000000 : ℝ), (1518196102531/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1672338861/5000000000 : ℝ)|^17 ≤ (23878208907147/100000000000000 : ℝ)^13
        have hw : |(-1672338861/5000000000 : ℝ)|=(1672338861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2393775437/5000000000 : ℝ)|^17 ≤ (19083444260011/50000000000000 : ℝ)^13
        have hw : |(2393775437/5000000000 : ℝ)|=(2393775437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2383601653/5000000000 : ℝ)|^17 ≤ (1518196102531/4000000000000 : ℝ)^13
        have hw : |(2383601653/5000000000 : ℝ)|=(2383601653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (691979689/1250000000 : ℝ)*x 0 + (9222261/1000000000 : ℝ)*x 1 + (6210037613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (691979689/1250000000 : ℝ)^17 ≤ (46149055990093/100000000000000 : ℝ)^13 := by
    have hnat : (691979689 : ℕ)^17*100000000000000^13 ≤ 46149055990093^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691979689 1250000000 46149055990093 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9222261/1000000000 : ℝ)^17 ≤ (27261110801/12500000000000 : ℝ)^13 := by
    have hnat : (9222261 : ℕ)^17*12500000000000^13 ≤ 27261110801^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9222261 1000000000 27261110801 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6210037613/10000000000 : ℝ)^17 ≤ (53632855110787/100000000000000 : ℝ)^13 := by
    have hnat : (6210037613 : ℕ)^17*100000000000000^13 ≤ 53632855110787^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6210037613 10000000000 53632855110787 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(691979689/1250000000 : ℝ), (9222261/1000000000 : ℝ), (6210037613/10000000000 : ℝ)] ![(46149055990093/100000000000000 : ℝ), (27261110801/12500000000000 : ℝ), (53632855110787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(691979689/1250000000 : ℝ)|^17 ≤ (46149055990093/100000000000000 : ℝ)^13
        have hw : |(691979689/1250000000 : ℝ)|=(691979689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9222261/1000000000 : ℝ)|^17 ≤ (27261110801/12500000000000 : ℝ)^13
        have hw : |(9222261/1000000000 : ℝ)|=(9222261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6210037613/10000000000 : ℝ)|^17 ≤ (53632855110787/100000000000000 : ℝ)^13
        have hw : |(6210037613/10000000000 : ℝ)|=(6210037613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (950359677/5000000000 : ℝ)*x 0 + (7651862641/10000000000 : ℝ)*x 1 + (-1354557351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (950359677/5000000000 : ℝ)^17 ≤ (11403721732963/100000000000000 : ℝ)^13 := by
    have hnat : (950359677 : ℕ)^17*100000000000000^13 ≤ 11403721732963^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950359677 5000000000 11403721732963 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7651862641/10000000000 : ℝ)^17 ≤ (3523491438769/5000000000000 : ℝ)^13 := by
    have hnat : (7651862641 : ℕ)^17*5000000000000^13 ≤ 3523491438769^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7651862641 10000000000 3523491438769 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354557351/5000000000 : ℝ)^17 ≤ (362528989539/2000000000000 : ℝ)^13 := by
    have hnat : (1354557351 : ℕ)^17*2000000000000^13 ≤ 362528989539^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354557351 5000000000 362528989539 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(950359677/5000000000 : ℝ), (7651862641/10000000000 : ℝ), (-1354557351/5000000000 : ℝ)] ![(11403721732963/100000000000000 : ℝ), (3523491438769/5000000000000 : ℝ), (362528989539/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(950359677/5000000000 : ℝ)|^17 ≤ (11403721732963/100000000000000 : ℝ)^13
        have hw : |(950359677/5000000000 : ℝ)|=(950359677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7651862641/10000000000 : ℝ)|^17 ≤ (3523491438769/5000000000000 : ℝ)^13
        have hw : |(7651862641/10000000000 : ℝ)|=(7651862641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1354557351/5000000000 : ℝ)|^17 ≤ (362528989539/2000000000000 : ℝ)^13
        have hw : |(-1354557351/5000000000 : ℝ)|=(1354557351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3343080301/10000000000 : ℝ)*x 0 + (2870741381/5000000000 : ℝ)*x 1 + (937557071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3343080301/10000000000 : ℝ)^17 ≤ (23863296748577/100000000000000 : ℝ)^13 := by
    have hnat : (3343080301 : ℕ)^17*100000000000000^13 ≤ 23863296748577^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3343080301 10000000000 23863296748577 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2870741381/5000000000 : ℝ)^17 ≤ (12100898898161/25000000000000 : ℝ)^13 := by
    have hnat : (2870741381 : ℕ)^17*25000000000000^13 ≤ 12100898898161^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870741381 5000000000 12100898898161 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937557071/2500000000 : ℝ)^17 ≤ (27733107635151/100000000000000 : ℝ)^13 := by
    have hnat : (937557071 : ℕ)^17*100000000000000^13 ≤ 27733107635151^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937557071 2500000000 27733107635151 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3343080301/10000000000 : ℝ), (2870741381/5000000000 : ℝ), (937557071/2500000000 : ℝ)] ![(23863296748577/100000000000000 : ℝ), (12100898898161/25000000000000 : ℝ), (27733107635151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3343080301/10000000000 : ℝ)|^17 ≤ (23863296748577/100000000000000 : ℝ)^13
        have hw : |(3343080301/10000000000 : ℝ)|=(3343080301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2870741381/5000000000 : ℝ)|^17 ≤ (12100898898161/25000000000000 : ℝ)^13
        have hw : |(2870741381/5000000000 : ℝ)|=(2870741381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937557071/2500000000 : ℝ)|^17 ≤ (27733107635151/100000000000000 : ℝ)^13
        have hw : |(937557071/2500000000 : ℝ)|=(937557071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-901374563/2000000000 : ℝ)*x 0 + (4973246017/10000000000 : ℝ)*x 1 + (427957229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901374563/2000000000 : ℝ)^17 ≤ (17633779249313/50000000000000 : ℝ)^13 := by
    have hnat : (901374563 : ℕ)^17*50000000000000^13 ≤ 17633779249313^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901374563 2000000000 17633779249313 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4973246017/10000000000 : ℝ)^17 ≤ (5014277911501/12500000000000 : ℝ)^13 := by
    have hnat : (4973246017 : ℕ)^17*12500000000000^13 ≤ 5014277911501^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4973246017 10000000000 5014277911501 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427957229/1250000000 : ℝ)^17 ≤ (12309109095843/50000000000000 : ℝ)^13 := by
    have hnat : (427957229 : ℕ)^17*50000000000000^13 ≤ 12309109095843^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427957229 1250000000 12309109095843 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901374563/2000000000 : ℝ), (4973246017/10000000000 : ℝ), (427957229/1250000000 : ℝ)] ![(17633779249313/50000000000000 : ℝ), (5014277911501/12500000000000 : ℝ), (12309109095843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901374563/2000000000 : ℝ)|^17 ≤ (17633779249313/50000000000000 : ℝ)^13
        have hw : |(-901374563/2000000000 : ℝ)|=(901374563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4973246017/10000000000 : ℝ)|^17 ≤ (5014277911501/12500000000000 : ℝ)^13
        have hw : |(4973246017/10000000000 : ℝ)|=(4973246017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427957229/1250000000 : ℝ)|^17 ≤ (12309109095843/50000000000000 : ℝ)^13
        have hw : |(427957229/1250000000 : ℝ)|=(427957229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6846957019/10000000000 : ℝ)*x 0 + (-70982289/5000000000 : ℝ)*x 1 + (193466057/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6846957019/10000000000 : ℝ)^17 ≤ (60937057455701/100000000000000 : ℝ)^13 := by
    have hnat : (6846957019 : ℕ)^17*100000000000000^13 ≤ 60937057455701^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6846957019 10000000000 60937057455701 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70982289/5000000000 : ℝ)^17 ≤ (383371650427/100000000000000 : ℝ)^13 := by
    have hnat : (70982289 : ℕ)^17*100000000000000^13 ≤ 383371650427^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70982289 5000000000 383371650427 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193466057/400000000 : ℝ)^17 ≤ (7735914176969/20000000000000 : ℝ)^13 := by
    have hnat : (193466057 : ℕ)^17*20000000000000^13 ≤ 7735914176969^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193466057 400000000 7735914176969 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6846957019/10000000000 : ℝ), (-70982289/5000000000 : ℝ), (193466057/400000000 : ℝ)] ![(60937057455701/100000000000000 : ℝ), (383371650427/100000000000000 : ℝ), (7735914176969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6846957019/10000000000 : ℝ)|^17 ≤ (60937057455701/100000000000000 : ℝ)^13
        have hw : |(6846957019/10000000000 : ℝ)|=(6846957019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70982289/5000000000 : ℝ)|^17 ≤ (383371650427/100000000000000 : ℝ)^13
        have hw : |(-70982289/5000000000 : ℝ)|=(70982289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(193466057/400000000 : ℝ)|^17 ≤ (7735914176969/20000000000000 : ℝ)^13
        have hw : |(193466057/400000000 : ℝ)|=(193466057/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2004876533/10000000000 : ℝ)*x 0 + (3028715883/5000000000 : ℝ)*x 1 + (-2282150989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004876533/10000000000 : ℝ)^17 ≤ (382116144587/3125000000000 : ℝ)^13 := by
    have hnat : (2004876533 : ℕ)^17*3125000000000^13 ≤ 382116144587^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004876533 10000000000 382116144587 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3028715883/5000000000 : ℝ)^17 ≤ (51915899892753/100000000000000 : ℝ)^13 := by
    have hnat : (3028715883 : ℕ)^17*100000000000000^13 ≤ 51915899892753^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3028715883 5000000000 51915899892753 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282150989/5000000000 : ℝ)^17 ≤ (17928191734743/50000000000000 : ℝ)^13 := by
    have hnat : (2282150989 : ℕ)^17*50000000000000^13 ≤ 17928191734743^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282150989 5000000000 17928191734743 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2004876533/10000000000 : ℝ), (3028715883/5000000000 : ℝ), (-2282150989/5000000000 : ℝ)] ![(382116144587/3125000000000 : ℝ), (51915899892753/100000000000000 : ℝ), (17928191734743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2004876533/10000000000 : ℝ)|^17 ≤ (382116144587/3125000000000 : ℝ)^13
        have hw : |(2004876533/10000000000 : ℝ)|=(2004876533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3028715883/5000000000 : ℝ)|^17 ≤ (51915899892753/100000000000000 : ℝ)^13
        have hw : |(3028715883/5000000000 : ℝ)|=(3028715883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282150989/5000000000 : ℝ)|^17 ≤ (17928191734743/50000000000000 : ℝ)^13
        have hw : |(-2282150989/5000000000 : ℝ)|=(2282150989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3170271933/10000000000 : ℝ)*x 0 + (1086225767/2000000000 : ℝ)*x 1 + (2128161251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3170271933/10000000000 : ℝ)^17 ≤ (2782901048851/12500000000000 : ℝ)^13 := by
    have hnat : (3170271933 : ℕ)^17*12500000000000^13 ≤ 2782901048851^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170271933 10000000000 2782901048851 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086225767/2000000000 : ℝ)^17 ≤ (45010913773409/100000000000000 : ℝ)^13 := by
    have hnat : (1086225767 : ℕ)^17*100000000000000^13 ≤ 45010913773409^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086225767 2000000000 45010913773409 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128161251/5000000000 : ℝ)^17 ≤ (32725877819227/100000000000000 : ℝ)^13 := by
    have hnat : (2128161251 : ℕ)^17*100000000000000^13 ≤ 32725877819227^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128161251 5000000000 32725877819227 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3170271933/10000000000 : ℝ), (1086225767/2000000000 : ℝ), (2128161251/5000000000 : ℝ)] ![(2782901048851/12500000000000 : ℝ), (45010913773409/100000000000000 : ℝ), (32725877819227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3170271933/10000000000 : ℝ)|^17 ≤ (2782901048851/12500000000000 : ℝ)^13
        have hw : |(3170271933/10000000000 : ℝ)|=(3170271933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086225767/2000000000 : ℝ)|^17 ≤ (45010913773409/100000000000000 : ℝ)^13
        have hw : |(1086225767/2000000000 : ℝ)|=(1086225767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2128161251/5000000000 : ℝ)|^17 ≤ (32725877819227/100000000000000 : ℝ)^13
        have hw : |(2128161251/5000000000 : ℝ)|=(2128161251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2565591653/10000000000 : ℝ)*x 0 + (6353488573/10000000000 : ℝ)*x 1 + (3763370551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2565591653/10000000000 : ℝ)^17 ≤ (16881035488759/100000000000000 : ℝ)^13 := by
    have hnat : (2565591653 : ℕ)^17*100000000000000^13 ≤ 16881035488759^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565591653 10000000000 16881035488759 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6353488573/10000000000 : ℝ)^17 ≤ (2210347873453/4000000000000 : ℝ)^13 := by
    have hnat : (6353488573 : ℕ)^17*4000000000000^13 ≤ 2210347873453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6353488573 10000000000 2210347873453 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3763370551/10000000000 : ℝ)^17 ≤ (1741266728303/6250000000000 : ℝ)^13 := by
    have hnat : (3763370551 : ℕ)^17*6250000000000^13 ≤ 1741266728303^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763370551 10000000000 1741266728303 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2565591653/10000000000 : ℝ), (6353488573/10000000000 : ℝ), (3763370551/10000000000 : ℝ)] ![(16881035488759/100000000000000 : ℝ), (2210347873453/4000000000000 : ℝ), (1741266728303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2565591653/10000000000 : ℝ)|^17 ≤ (16881035488759/100000000000000 : ℝ)^13
        have hw : |(-2565591653/10000000000 : ℝ)|=(2565591653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6353488573/10000000000 : ℝ)|^17 ≤ (2210347873453/4000000000000 : ℝ)^13
        have hw : |(6353488573/10000000000 : ℝ)|=(6353488573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3763370551/10000000000 : ℝ)|^17 ≤ (1741266728303/6250000000000 : ℝ)^13
        have hw : |(3763370551/10000000000 : ℝ)|=(3763370551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1898353587/2500000000 : ℝ)*x 0 + (11652681/5000000000 : ℝ)*x 1 + (1000614837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898353587/2500000000 : ℝ)^17 ≤ (13953350679349/20000000000000 : ℝ)^13 := by
    have hnat : (1898353587 : ℕ)^17*20000000000000^13 ≤ 13953350679349^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898353587 2500000000 13953350679349 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11652681/5000000000 : ℝ)^17 ≤ (3609460301/10000000000000 : ℝ)^13 := by
    have hnat : (11652681 : ℕ)^17*10000000000000^13 ≤ 3609460301^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11652681 5000000000 3609460301 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000614837/2500000000 : ℝ)^17 ≤ (3774643998321/12500000000000 : ℝ)^13 := by
    have hnat : (1000614837 : ℕ)^17*12500000000000^13 ≤ 3774643998321^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000614837 2500000000 3774643998321 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1898353587/2500000000 : ℝ), (11652681/5000000000 : ℝ), (1000614837/2500000000 : ℝ)] ![(13953350679349/20000000000000 : ℝ), (3609460301/10000000000000 : ℝ), (3774643998321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1898353587/2500000000 : ℝ)|^17 ≤ (13953350679349/20000000000000 : ℝ)^13
        have hw : |(1898353587/2500000000 : ℝ)|=(1898353587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11652681/5000000000 : ℝ)|^17 ≤ (3609460301/10000000000000 : ℝ)^13
        have hw : |(11652681/5000000000 : ℝ)|=(11652681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000614837/2500000000 : ℝ)|^17 ≤ (3774643998321/12500000000000 : ℝ)^13
        have hw : |(1000614837/2500000000 : ℝ)|=(1000614837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1030297041/5000000000 : ℝ)*x 0 + (731233311/1000000000 : ℝ)*x 1 + (-3022608479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030297041/5000000000 : ℝ)^17 ≤ (6336992685403/50000000000000 : ℝ)^13 := by
    have hnat : (1030297041 : ℕ)^17*50000000000000^13 ≤ 6336992685403^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030297041 5000000000 6336992685403 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (731233311/1000000000 : ℝ)^17 ≤ (6640901430019/10000000000000 : ℝ)^13 := by
    have hnat : (731233311 : ℕ)^17*10000000000000^13 ≤ 6640901430019^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731233311 1000000000 6640901430019 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3022608479/10000000000 : ℝ)^17 ≤ (10458500155089/50000000000000 : ℝ)^13 := by
    have hnat : (3022608479 : ℕ)^17*50000000000000^13 ≤ 10458500155089^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022608479 10000000000 10458500155089 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030297041/5000000000 : ℝ), (731233311/1000000000 : ℝ), (-3022608479/10000000000 : ℝ)] ![(6336992685403/50000000000000 : ℝ), (6640901430019/10000000000000 : ℝ), (10458500155089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030297041/5000000000 : ℝ)|^17 ≤ (6336992685403/50000000000000 : ℝ)^13
        have hw : |(1030297041/5000000000 : ℝ)|=(1030297041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(731233311/1000000000 : ℝ)|^17 ≤ (6640901430019/10000000000000 : ℝ)^13
        have hw : |(731233311/1000000000 : ℝ)|=(731233311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3022608479/10000000000 : ℝ)|^17 ≤ (10458500155089/50000000000000 : ℝ)^13
        have hw : |(-3022608479/10000000000 : ℝ)|=(3022608479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304023_s2_s2_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2957023081/5000000000 : ℝ)*x 0 + (3768248429/10000000000 : ℝ)*x 1 + (3117270869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2957023081/5000000000 : ℝ)^17 ≤ (62893447777/125000000000 : ℝ)^13 := by
    have hnat : (2957023081 : ℕ)^17*125000000000^13 ≤ 62893447777^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957023081 5000000000 62893447777 125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3768248429/10000000000 : ℝ)^17 ≤ (27907499113029/100000000000000 : ℝ)^13 := by
    have hnat : (3768248429 : ℕ)^17*100000000000000^13 ≤ 27907499113029^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3768248429 10000000000 27907499113029 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3117270869/10000000000 : ℝ)^17 ≤ (272221783123/1250000000000 : ℝ)^13 := by
    have hnat : (3117270869 : ℕ)^17*1250000000000^13 ≤ 272221783123^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117270869 10000000000 272221783123 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2957023081/5000000000 : ℝ), (3768248429/10000000000 : ℝ), (3117270869/10000000000 : ℝ)] ![(62893447777/125000000000 : ℝ), (27907499113029/100000000000000 : ℝ), (272221783123/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2957023081/5000000000 : ℝ)|^17 ≤ (62893447777/125000000000 : ℝ)^13
        have hw : |(2957023081/5000000000 : ℝ)|=(2957023081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3768248429/10000000000 : ℝ)|^17 ≤ (27907499113029/100000000000000 : ℝ)^13
        have hw : |(3768248429/10000000000 : ℝ)|=(3768248429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3117270869/10000000000 : ℝ)|^17 ≤ (272221783123/1250000000000 : ℝ)^13
        have hw : |(3117270869/10000000000 : ℝ)|=(3117270869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304023_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38237/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38237/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7519/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(7519/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85819/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85819/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7501/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7501/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(881/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(881/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33949/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33949/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (38237/50000 : ℝ) ^ (33/8 : ℝ) ≤ (1322983549444269989/4000000000000000000 : ℝ) := by
    have hpowers : (38237/50000 : ℝ)^33 ≤ (1322983549444269989/4000000000000000000 : ℝ)^8 := by
      have hnat : (38237 : ℕ)^33*4000000000000000000^8 ≤ 1322983549444269989^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38237 50000 1322983549444269989 4000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38237/50000 : ℝ)) (X := (1322983549444269989/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (5322983549444269989/4000000000000000000 : ℝ) ≤ (10717257574978631/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5322983549444269989/4000000000000000000 : ℝ)^8 ≤ (10717257574978631/10000000000000000 : ℝ)^33 := by
      have hnat : (5322983549444269989 : ℕ)^8*10000000000000000^33 ≤ 10717257574978631^33*4000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5322983549444269989 4000000000000000000 10717257574978631 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10717257574978631/10000000000000000 : ℝ)) (X := (5322983549444269989/4000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (3322983549444269989/2000000000000000000 : ℝ) ≤ (2261955744805569/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3322983549444269989/2000000000000000000 : ℝ)^8 ≤ (2261955744805569/2000000000000000 : ℝ)^33 := by
      have hnat : (3322983549444269989 : ℕ)^8*2000000000000000^33 ≤ 2261955744805569^33*2000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3322983549444269989 2000000000000000000 2261955744805569 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2261955744805569/2000000000000000 : ℝ)) (X := (3322983549444269989/2000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(717257574978631/7647400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(296260574524607/3823700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (38237/50000 : ℝ)) (alpha := (717257574978631/7647400000000000 : ℝ)) (beta := (296260574524607/3823700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38237/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(717257574978631/7647400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(296260574524607/3823700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (7519/20000 : ℝ) ^ (33/8 : ℝ) ≤ (1767712438290203569/100000000000000000000 : ℝ) := by
    have hpowers : (7519/20000 : ℝ)^33 ≤ (1767712438290203569/100000000000000000000 : ℝ)^8 := by
      have hnat : (7519 : ℕ)^33*100000000000000000000^8 ≤ 1767712438290203569^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7519 20000 1767712438290203569 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7519/20000 : ℝ)) (X := (1767712438290203569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (101767712438290203569/100000000000000000000 : ℝ) ≤ (627660601748533/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101767712438290203569/100000000000000000000 : ℝ)^8 ≤ (627660601748533/625000000000000 : ℝ)^33 := by
      have hnat : (101767712438290203569 : ℕ)^8*625000000000000^33 ≤ 627660601748533^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101767712438290203569 100000000000000000000 627660601748533 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627660601748533/625000000000000 : ℝ)) (X := (101767712438290203569/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (51767712438290203569/50000000000000000000 : ℝ) ≤ (10084582707336151/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (51767712438290203569/50000000000000000000 : ℝ)^8 ≤ (10084582707336151/10000000000000000 : ℝ)^33 := by
      have hnat : (51767712438290203569 : ℕ)^8*10000000000000000^33 ≤ 10084582707336151^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51767712438290203569 50000000000000000000 10084582707336151 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10084582707336151/10000000000000000 : ℝ)) (X := (51767712438290203569/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2660601748533/234968750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(42013079359623/3759500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (7519/20000 : ℝ)) (alpha := (2660601748533/234968750000000 : ℝ)) (beta := (42013079359623/3759500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (7519/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2660601748533/234968750000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(42013079359623/3759500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (85819/100000 : ℝ) ^ (33/8 : ℝ) ≤ (53214713677151845247/100000000000000000000 : ℝ) := by
    have hpowers : (85819/100000 : ℝ)^33 ≤ (53214713677151845247/100000000000000000000 : ℝ)^8 := by
      have hnat : (85819 : ℕ)^33*100000000000000000000^8 ≤ 53214713677151845247^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85819 100000 53214713677151845247 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85819/100000 : ℝ)) (X := (53214713677151845247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (153214713677151845247/100000000000000000000 : ℝ) ≤ (5544869525287943/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (153214713677151845247/100000000000000000000 : ℝ)^8 ≤ (5544869525287943/5000000000000000 : ℝ)^33 := by
      have hnat : (153214713677151845247 : ℕ)^8*5000000000000000^33 ≤ 5544869525287943^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153214713677151845247 100000000000000000000 5544869525287943 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5544869525287943/5000000000000000 : ℝ)) (X := (153214713677151845247/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (103214713677151845247/50000000000000000000 : ℝ) ≤ (2384175738309207/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (103214713677151845247/50000000000000000000 : ℝ)^8 ≤ (2384175738309207/2000000000000000 : ℝ)^33 := by
      have hnat : (103214713677151845247 : ℕ)^8*2000000000000000^33 ≤ 2384175738309207^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103214713677151845247 50000000000000000000 2384175738309207 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2384175738309207/2000000000000000 : ℝ)) (X := (103214713677151845247/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(544869525287943/4290950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(831139640970149/8581900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (85819/100000 : ℝ)) (alpha := (544869525287943/4290950000000000 : ℝ)) (beta := (831139640970149/8581900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (85819/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(544869525287943/4290950000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(831139640970149/8581900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((3032784783/10000000000 : ℝ)*X 2 0+(1556163689/2500000000 : ℝ)*X 2 1+(-139384151/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((853259239/2000000000 : ℝ)*X 0 0+(76365687/156250000 : ℝ)*X 0 1+(150957533/400000000 : ℝ)*X 0 2+(853259239/2000000000 : ℝ)*X 1 0+(76365687/156250000 : ℝ)*X 1 1+(150957533/400000000 : ℝ)*X 1 2+(853259239/2000000000 : ℝ)*X 2 0+(76365687/156250000 : ℝ)*X 2 1+(150957533/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1672338861/5000000000 : ℝ)*X 0 0+(2393775437/5000000000 : ℝ)*X 0 1+(2383601653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((691979689/1250000000 : ℝ)*X 1 0+(9222261/1000000000 : ℝ)*X 1 1+(6210037613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((950359677/5000000000 : ℝ)*X 2 0+(7651862641/10000000000 : ℝ)*X 2 1+(-1354557351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((3343080301/10000000000 : ℝ)*X 0 0+(2870741381/5000000000 : ℝ)*X 0 1+(937557071/2500000000 : ℝ)*X 0 2+(3343080301/10000000000 : ℝ)*X 1 0+(2870741381/5000000000 : ℝ)*X 1 1+(937557071/2500000000 : ℝ)*X 1 2+(3343080301/10000000000 : ℝ)*X 2 0+(2870741381/5000000000 : ℝ)*X 2 1+(937557071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-901374563/2000000000 : ℝ)*X 0 0+(4973246017/10000000000 : ℝ)*X 0 1+(427957229/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((6846957019/10000000000 : ℝ)*X 1 0+(-70982289/5000000000 : ℝ)*X 1 1+(193466057/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2004876533/10000000000 : ℝ)*X 2 0+(3028715883/5000000000 : ℝ)*X 2 1+(-2282150989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((3170271933/10000000000 : ℝ)*X 0 0+(1086225767/2000000000 : ℝ)*X 0 1+(2128161251/5000000000 : ℝ)*X 0 2+(3170271933/10000000000 : ℝ)*X 1 0+(1086225767/2000000000 : ℝ)*X 1 1+(2128161251/5000000000 : ℝ)*X 1 2+(3170271933/10000000000 : ℝ)*X 2 0+(1086225767/2000000000 : ℝ)*X 2 1+(2128161251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-2565591653/10000000000 : ℝ)*X 0 0+(6353488573/10000000000 : ℝ)*X 0 1+(3763370551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((1898353587/2500000000 : ℝ)*X 1 0+(11652681/5000000000 : ℝ)*X 1 1+(1000614837/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1030297041/5000000000 : ℝ)*X 2 0+(731233311/1000000000 : ℝ)*X 2 1+(-3022608479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((2957023081/5000000000 : ℝ)*X 0 0+(3768248429/10000000000 : ℝ)*X 0 1+(3117270869/10000000000 : ℝ)*X 0 2+(2957023081/5000000000 : ℝ)*X 1 0+(3768248429/10000000000 : ℝ)*X 1 1+(3117270869/10000000000 : ℝ)*X 1 2+(2957023081/5000000000 : ℝ)*X 2 0+(3768248429/10000000000 : ℝ)*X 2 1+(3117270869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304023_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((7501/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7501/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (94168545869092799267196074722863/6168326508364250000000000000000000000 : ℝ) := by norm_num
    linear_combination (130430917653/250000000000 : ℝ)*(base7) + (1131978964713/1000000000000 : ℝ)*(base49) + (171701090921/200000000000 : ℝ)*(base50) + (45357048121/500000000000 : ℝ)*(base60) + (1529809782627/500000000000 : ℝ)*(major_s2_0) + (1529809782627/500000000000 : ℝ)*(major_s2_1) + (1529809782627/500000000000 : ℝ)*(major_s2_2) + (943819108463/250000000000 : ℝ)*(sp_s2_7) + (943834464593/250000000000 : ℝ)*(sp_s2_8) + (151009014369/40000000000 : ℝ)*(sp_s2_9) + (2538924275919/1000000000000 : ℝ)*(sp_s2_12) + (60039541/1000000000000 : ℝ)*(sp_s2_19) + (61424519/1000000000000 : ℝ)*(sp_s2_20) + (112499147/1000000000000 : ℝ)*(sp_s2_22) + (126078790303/62500000000 : ℝ)*(f.failure) + (943834464593/250000000000 : ℝ)*(f.sum) + (45356974027567281799/161318265250000000000000000000000 : ℝ)*base62 + (4993783787009863/4290950000000000000000000000 : ℝ)*base65 + (898843681809927/939875000000000000000000000 : ℝ)*base67 + (14549357285449/2145475000000000000000000000 : ℝ)*base68 + (31714033030233585043/65629222060000000000000000000000 : ℝ)*base71 + (493888780564999/1911850000000000000000000000 : ℝ)*base73 + (181869115027461/469937500000000000000000000 : ℝ)*base75 + (1179113857126677/3823700000000000000000000000 : ℝ)*base77 + (32312432592477194153/71876000750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (221/1562500000000000 : ℝ)*base86 + (221/1562500000000000 : ℝ)*base88 + (221/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(881/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(881/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (297829801099685258163944628831/77104081354553125000000000000000000 : ℝ) := by norm_num
    linear_combination (58102308769/200000000000 : ℝ)*(base40) + (24389729643/50000000000 : ℝ)*(base49) + (429217/500000000000 : ℝ)*(base60) + (24468444847/12500000000 : ℝ)*(major_s2_0) + (24468444847/12500000000 : ℝ)*(major_s2_1) + (24468444847/12500000000 : ℝ)*(major_s2_2) + (188947/250000000000 : ℝ)*(sp_s2_2) + (3304927/62500000000 : ℝ)*(sp_s2_6) + (35547951/1000000000000 : ℝ)*(sp_s2_8) + (1312176013467/500000000000 : ℝ)*(sp_s2_13) + (32803866859/12500000000 : ℝ)*(sp_s2_14) + (524870254229/200000000000 : ℝ)*(sp_s2_15) + (161318122773/125000000000 : ℝ)*(sp_s2_19) + (3565131/500000000000 : ℝ)*(sp_s2_21) + (161324732627/125000000000 : ℝ)*(f.failure) + (1312176013467/500000000000 : ℝ)*(f.sum) + (5527228554936172711/16131826525000000000000000000000 : ℝ)*base62 + (15815534258719/429095000000000000000000000 : ℝ)*base65 + (5264578143471/46993750000000000000000000 : ℝ)*base66 + (32481969544173/107273750000000000000000000 : ℝ)*base68 + (680521179336032559/3281461103000000000000000000000 : ℝ)*base71 + (106319388288073/382370000000000000000000000 : ℝ)*base73 + (32472265966323/375950000000000000000000000 : ℝ)*base74 + (3872524306709/38237000000000000000000000 : ℝ)*base76 + (1850787895371563497/7187600075000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (293/1562500000000000 : ℝ)*base87 + (293/1562500000000000 : ℝ)*base89 + (293/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33949/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33949/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (133459693129903530371813268618177/12336653016728500000000000000000000000 : ℝ) := by norm_num
    linear_combination (541418396363/1000000000000 : ℝ)*(base7) + (5972829/1000000000000 : ℝ)*(base11) + (203234794259/500000000000 : ℝ)*(base40) + (8279123213/8000000000 : ℝ)*(base49) + (825314447869/1000000000000 : ℝ)*(base50) + (3335477746089/1000000000000 : ℝ)*(major_s2_0) + (3335477746089/1000000000000 : ℝ)*(major_s2_1) + (3335477746089/1000000000000 : ℝ)*(major_s2_2) + (49515681/500000000000 : ℝ)*(sp_s2_2) + (305739631/1000000000000 : ℝ)*(sp_s2_9) + (4132841333911/1000000000000 : ℝ)*(sp_s2_20) + (206642365337/50000000000 : ℝ)*(sp_s2_21) + (1033110633937/250000000000 : ℝ)*(sp_s2_22) + (2740557160333/1000000000000 : ℝ)*(sp_s2_25) + (219913876397/100000000000 : ℝ)*(f.failure) + (206642365337/50000000000 : ℝ)*(f.sum) + (55331995379098068633/80659132625000000000000000000000 : ℝ)*base63 + (7596810332103861/8581900000000000000000000000 : ℝ)*base65 + (2560471730864453/3759500000000000000000000000 : ℝ)*base67 + (4463797166431657/4290950000000000000000000000 : ℝ)*base69 + (44000837798836604143/131258444120000000000000000000000 : ℝ)*base71 + (2483467609246133/3823700000000000000000000000 : ℝ)*base73 + (967807382188527/939875000000000000000000000 : ℝ)*base75 + (1842314239856959/7647400000000000000000000000 : ℝ)*base77 + (8770517268720727199/35938000375000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (527/1250000000000000 : ℝ)*base86 + (527/1250000000000000 : ℝ)*base88 + (527/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38237/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38237/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7519/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(7519/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85819/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85819/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7501/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7501/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(881/6250 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(881/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33949/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33949/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304023_s2 p hpa hpb X hX hprev1

#print axioms solution
