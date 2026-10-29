-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307083_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:14.39182+00:00
-- url     : https://prove2.me/submissions/e6901f1e-dd00-4484-a3fa-8d2b49df8abf

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
theorem collision_support_c307083_s2_s2_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1212893859/5000000000 : ℝ)*x 0 + (2495254963/5000000000 : ℝ)*x 1 + (1067803303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1212893859/5000000000 : ℝ)^17 ≤ (15688330472477/100000000000000 : ℝ)^13 := by
    have hnat : (1212893859 : ℕ)^17*100000000000000^13 ≤ 15688330472477^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212893859 5000000000 15688330472477 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495254963/5000000000 : ℝ)^17 ≤ (2518526100949/6250000000000 : ℝ)^13 := by
    have hnat : (2495254963 : ℕ)^17*6250000000000^13 ≤ 2518526100949^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495254963 5000000000 2518526100949 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067803303/2000000000 : ℝ)^17 ≤ (44015251903627/100000000000000 : ℝ)^13 := by
    have hnat : (1067803303 : ℕ)^17*100000000000000^13 ≤ 44015251903627^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067803303 2000000000 44015251903627 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1212893859/5000000000 : ℝ), (2495254963/5000000000 : ℝ), (1067803303/2000000000 : ℝ)] ![(15688330472477/100000000000000 : ℝ), (2518526100949/6250000000000 : ℝ), (44015251903627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1212893859/5000000000 : ℝ)|^17 ≤ (15688330472477/100000000000000 : ℝ)^13
        have hw : |(-1212893859/5000000000 : ℝ)|=(1212893859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495254963/5000000000 : ℝ)|^17 ≤ (2518526100949/6250000000000 : ℝ)^13
        have hw : |(2495254963/5000000000 : ℝ)|=(2495254963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1067803303/2000000000 : ℝ)|^17 ≤ (44015251903627/100000000000000 : ℝ)^13
        have hw : |(1067803303/2000000000 : ℝ)|=(1067803303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6863325449/10000000000 : ℝ)*x 0 + (-499839427/5000000000 : ℝ)*x 1 + (2188798949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6863325449/10000000000 : ℝ)^17 ≤ (61127628135139/100000000000000 : ℝ)^13 := by
    have hnat : (6863325449 : ℕ)^17*100000000000000^13 ≤ 61127628135139^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6863325449 10000000000 61127628135139 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499839427/5000000000 : ℝ)^17 ≤ (4921814899373/100000000000000 : ℝ)^13 := by
    have hnat : (499839427 : ℕ)^17*100000000000000^13 ≤ 4921814899373^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499839427 5000000000 4921814899373 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188798949/5000000000 : ℝ)^17 ≤ (3395055695449/10000000000000 : ℝ)^13 := by
    have hnat : (2188798949 : ℕ)^17*10000000000000^13 ≤ 3395055695449^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188798949 5000000000 3395055695449 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6863325449/10000000000 : ℝ), (-499839427/5000000000 : ℝ), (2188798949/5000000000 : ℝ)] ![(61127628135139/100000000000000 : ℝ), (4921814899373/100000000000000 : ℝ), (3395055695449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6863325449/10000000000 : ℝ)|^17 ≤ (61127628135139/100000000000000 : ℝ)^13
        have hw : |(6863325449/10000000000 : ℝ)|=(6863325449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499839427/5000000000 : ℝ)|^17 ≤ (4921814899373/100000000000000 : ℝ)^13
        have hw : |(-499839427/5000000000 : ℝ)|=(499839427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2188798949/5000000000 : ℝ)|^17 ≤ (3395055695449/10000000000000 : ℝ)^13
        have hw : |(2188798949/5000000000 : ℝ)|=(2188798949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3764103517/10000000000 : ℝ)*x 0 + (6377269001/10000000000 : ℝ)*x 1 + (-2533252203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3764103517/10000000000 : ℝ)^17 ≤ (27867363605567/100000000000000 : ℝ)^13 := by
    have hnat : (3764103517 : ℕ)^17*100000000000000^13 ≤ 27867363605567^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764103517 10000000000 27867363605567 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6377269001/10000000000 : ℝ)^17 ≤ (11105863806431/20000000000000 : ℝ)^13 := by
    have hnat : (6377269001 : ℕ)^17*20000000000000^13 ≤ 11105863806431^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6377269001 10000000000 11105863806431 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2533252203/10000000000 : ℝ)^17 ≤ (16603317340731/100000000000000 : ℝ)^13 := by
    have hnat : (2533252203 : ℕ)^17*100000000000000^13 ≤ 16603317340731^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533252203 10000000000 16603317340731 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3764103517/10000000000 : ℝ), (6377269001/10000000000 : ℝ), (-2533252203/10000000000 : ℝ)] ![(27867363605567/100000000000000 : ℝ), (11105863806431/20000000000000 : ℝ), (16603317340731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3764103517/10000000000 : ℝ)|^17 ≤ (27867363605567/100000000000000 : ℝ)^13
        have hw : |(3764103517/10000000000 : ℝ)|=(3764103517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6377269001/10000000000 : ℝ)|^17 ≤ (11105863806431/20000000000000 : ℝ)^13
        have hw : |(6377269001/10000000000 : ℝ)|=(6377269001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2533252203/10000000000 : ℝ)|^17 ≤ (16603317340731/100000000000000 : ℝ)^13
        have hw : |(-2533252203/10000000000 : ℝ)|=(2533252203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1223500907/5000000000 : ℝ)*x 0 + (2479226153/5000000000 : ℝ)*x 1 + (214148539/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1223500907/5000000000 : ℝ)^17 ≤ (7933992212883/50000000000000 : ℝ)^13 := by
    have hnat : (1223500907 : ℕ)^17*50000000000000^13 ≤ 7933992212883^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223500907 5000000000 7933992212883 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2479226153/5000000000 : ℝ)^17 ≤ (19979126441511/50000000000000 : ℝ)^13 := by
    have hnat : (2479226153 : ℕ)^17*50000000000000^13 ≤ 19979126441511^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479226153 5000000000 19979126441511 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214148539/400000000 : ℝ)^17 ≤ (22086881336989/50000000000000 : ℝ)^13 := by
    have hnat : (214148539 : ℕ)^17*50000000000000^13 ≤ 22086881336989^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214148539 400000000 22086881336989 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1223500907/5000000000 : ℝ), (2479226153/5000000000 : ℝ), (214148539/400000000 : ℝ)] ![(7933992212883/50000000000000 : ℝ), (19979126441511/50000000000000 : ℝ), (22086881336989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1223500907/5000000000 : ℝ)|^17 ≤ (7933992212883/50000000000000 : ℝ)^13
        have hw : |(-1223500907/5000000000 : ℝ)|=(1223500907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2479226153/5000000000 : ℝ)|^17 ≤ (19979126441511/50000000000000 : ℝ)^13
        have hw : |(2479226153/5000000000 : ℝ)|=(2479226153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(214148539/400000000 : ℝ)|^17 ≤ (22086881336989/50000000000000 : ℝ)^13
        have hw : |(214148539/400000000 : ℝ)|=(214148539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (806801381/1250000000 : ℝ)*x 0 + (-16365309/5000000000 : ℝ)*x 1 + (661794387/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806801381/1250000000 : ℝ)^17 ≤ (28204666497977/50000000000000 : ℝ)^13 := by
    have hnat : (806801381 : ℕ)^17*50000000000000^13 ≤ 28204666497977^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806801381 1250000000 28204666497977 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16365309/5000000000 : ℝ)^17 ≤ (56276195573/100000000000000 : ℝ)^13 := by
    have hnat : (16365309 : ℕ)^17*100000000000000^13 ≤ 56276195573^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16365309 5000000000 56276195573 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (661794387/1250000000 : ℝ)^17 ≤ (21767195394087/50000000000000 : ℝ)^13 := by
    have hnat : (661794387 : ℕ)^17*50000000000000^13 ≤ 21767195394087^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661794387 1250000000 21767195394087 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(806801381/1250000000 : ℝ), (-16365309/5000000000 : ℝ), (661794387/1250000000 : ℝ)] ![(28204666497977/50000000000000 : ℝ), (56276195573/100000000000000 : ℝ), (21767195394087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(806801381/1250000000 : ℝ)|^17 ≤ (28204666497977/50000000000000 : ℝ)^13
        have hw : |(806801381/1250000000 : ℝ)|=(806801381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16365309/5000000000 : ℝ)|^17 ≤ (56276195573/100000000000000 : ℝ)^13
        have hw : |(-16365309/5000000000 : ℝ)|=(16365309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(661794387/1250000000 : ℝ)|^17 ≤ (21767195394087/50000000000000 : ℝ)^13
        have hw : |(661794387/1250000000 : ℝ)|=(661794387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (196464549/625000000 : ℝ)*x 0 + (7457910461/10000000000 : ℝ)*x 1 + (-339593279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196464549/625000000 : ℝ)^17 ≤ (22017059194057/100000000000000 : ℝ)^13 := by
    have hnat : (196464549 : ℕ)^17*100000000000000^13 ≤ 22017059194057^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196464549 625000000 22017059194057 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7457910461/10000000000 : ℝ)^17 ≤ (68143187813369/100000000000000 : ℝ)^13 := by
    have hnat : (7457910461 : ℕ)^17*100000000000000^13 ≤ 68143187813369^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7457910461 10000000000 68143187813369 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339593279/2000000000 : ℝ)^17 ≤ (9839752972233/100000000000000 : ℝ)^13 := by
    have hnat : (339593279 : ℕ)^17*100000000000000^13 ≤ 9839752972233^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339593279 2000000000 9839752972233 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(196464549/625000000 : ℝ), (7457910461/10000000000 : ℝ), (-339593279/2000000000 : ℝ)] ![(22017059194057/100000000000000 : ℝ), (68143187813369/100000000000000 : ℝ), (9839752972233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(196464549/625000000 : ℝ)|^17 ≤ (22017059194057/100000000000000 : ℝ)^13
        have hw : |(196464549/625000000 : ℝ)|=(196464549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7457910461/10000000000 : ℝ)|^17 ≤ (68143187813369/100000000000000 : ℝ)^13
        have hw : |(7457910461/10000000000 : ℝ)|=(7457910461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339593279/2000000000 : ℝ)|^17 ≤ (9839752972233/100000000000000 : ℝ)^13
        have hw : |(-339593279/2000000000 : ℝ)|=(339593279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (370496301/1250000000 : ℝ)*x 0 + (4834960127/10000000000 : ℝ)*x 1 + (5052305937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370496301/1250000000 : ℝ)^17 ≤ (20387947831201/100000000000000 : ℝ)^13 := by
    have hnat : (370496301 : ℕ)^17*100000000000000^13 ≤ 20387947831201^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370496301 1250000000 20387947831201 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4834960127/10000000000 : ℝ)^17 ≤ (7732376898979/20000000000000 : ℝ)^13 := by
    have hnat : (4834960127 : ℕ)^17*20000000000000^13 ≤ 7732376898979^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834960127 10000000000 7732376898979 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5052305937/10000000000 : ℝ)^17 ≤ (10237541916667/25000000000000 : ℝ)^13 := by
    have hnat : (5052305937 : ℕ)^17*25000000000000^13 ≤ 10237541916667^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052305937 10000000000 10237541916667 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(370496301/1250000000 : ℝ), (4834960127/10000000000 : ℝ), (5052305937/10000000000 : ℝ)] ![(20387947831201/100000000000000 : ℝ), (7732376898979/20000000000000 : ℝ), (10237541916667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(370496301/1250000000 : ℝ)|^17 ≤ (20387947831201/100000000000000 : ℝ)^13
        have hw : |(370496301/1250000000 : ℝ)|=(370496301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4834960127/10000000000 : ℝ)|^17 ≤ (7732376898979/20000000000000 : ℝ)^13
        have hw : |(4834960127/10000000000 : ℝ)|=(4834960127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5052305937/10000000000 : ℝ)|^17 ≤ (10237541916667/25000000000000 : ℝ)^13
        have hw : |(5052305937/10000000000 : ℝ)|=(5052305937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1430840307/10000000000 : ℝ)*x 0 + (952972723/2500000000 : ℝ)*x 1 + (7091848997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1430840307/10000000000 : ℝ)^17 ≤ (1573269265543/20000000000000 : ℝ)^13 := by
    have hnat : (1430840307 : ℕ)^17*20000000000000^13 ≤ 1573269265543^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430840307 10000000000 1573269265543 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952972723/2500000000 : ℝ)^17 ≤ (1770682196241/6250000000000 : ℝ)^13 := by
    have hnat : (952972723 : ℕ)^17*6250000000000^13 ≤ 1770682196241^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952972723 2500000000 1770682196241 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7091848997/10000000000 : ℝ)^17 ≤ (498458894693/781250000000 : ℝ)^13 := by
    have hnat : (7091848997 : ℕ)^17*781250000000^13 ≤ 498458894693^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7091848997 10000000000 498458894693 781250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1430840307/10000000000 : ℝ), (952972723/2500000000 : ℝ), (7091848997/10000000000 : ℝ)] ![(1573269265543/20000000000000 : ℝ), (1770682196241/6250000000000 : ℝ), (498458894693/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1430840307/10000000000 : ℝ)|^17 ≤ (1573269265543/20000000000000 : ℝ)^13
        have hw : |(-1430840307/10000000000 : ℝ)|=(1430840307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(952972723/2500000000 : ℝ)|^17 ≤ (1770682196241/6250000000000 : ℝ)^13
        have hw : |(952972723/2500000000 : ℝ)|=(952972723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7091848997/10000000000 : ℝ)|^17 ≤ (498458894693/781250000000 : ℝ)^13
        have hw : |(7091848997/10000000000 : ℝ)|=(7091848997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4031287097/5000000000 : ℝ)*x 0 + (-351408241/5000000000 : ℝ)*x 1 + (3080103037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4031287097/5000000000 : ℝ)^17 ≤ (9432057106193/12500000000000 : ℝ)^13 := by
    have hnat : (4031287097 : ℕ)^17*12500000000000^13 ≤ 9432057106193^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031287097 5000000000 9432057106193 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351408241/5000000000 : ℝ)^17 ≤ (3104731674939/100000000000000 : ℝ)^13 := by
    have hnat : (351408241 : ℕ)^17*100000000000000^13 ≤ 3104731674939^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351408241 5000000000 3104731674939 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3080103037/10000000000 : ℝ)^17 ≤ (21438811459159/100000000000000 : ℝ)^13 := by
    have hnat : (3080103037 : ℕ)^17*100000000000000^13 ≤ 21438811459159^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080103037 10000000000 21438811459159 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4031287097/5000000000 : ℝ), (-351408241/5000000000 : ℝ), (3080103037/10000000000 : ℝ)] ![(9432057106193/12500000000000 : ℝ), (3104731674939/100000000000000 : ℝ), (21438811459159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4031287097/5000000000 : ℝ)|^17 ≤ (9432057106193/12500000000000 : ℝ)^13
        have hw : |(4031287097/5000000000 : ℝ)|=(4031287097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-351408241/5000000000 : ℝ)|^17 ≤ (3104731674939/100000000000000 : ℝ)^13
        have hw : |(-351408241/5000000000 : ℝ)|=(351408241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3080103037/10000000000 : ℝ)|^17 ≤ (21438811459159/100000000000000 : ℝ)^13
        have hw : |(3080103037/10000000000 : ℝ)|=(3080103037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3969889969/10000000000 : ℝ)*x 0 + (3417231511/5000000000 : ℝ)*x 1 + (-203819977/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3969889969/10000000000 : ℝ)^17 ≤ (1493811146361/5000000000000 : ℝ)^13 := by
    have hnat : (3969889969 : ℕ)^17*5000000000000^13 ≤ 1493811146361^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3969889969 10000000000 1493811146361 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3417231511/5000000000 : ℝ)^17 ≤ (7598961180289/12500000000000 : ℝ)^13 := by
    have hnat : (3417231511 : ℕ)^17*12500000000000^13 ≤ 7598961180289^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3417231511 5000000000 7598961180289 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203819977/1250000000 : ℝ)^17 ≤ (9332087616541/100000000000000 : ℝ)^13 := by
    have hnat : (203819977 : ℕ)^17*100000000000000^13 ≤ 9332087616541^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203819977 1250000000 9332087616541 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3969889969/10000000000 : ℝ), (3417231511/5000000000 : ℝ), (-203819977/1250000000 : ℝ)] ![(1493811146361/5000000000000 : ℝ), (7598961180289/12500000000000 : ℝ), (9332087616541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3969889969/10000000000 : ℝ)|^17 ≤ (1493811146361/5000000000000 : ℝ)^13
        have hw : |(3969889969/10000000000 : ℝ)|=(3969889969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3417231511/5000000000 : ℝ)|^17 ≤ (7598961180289/12500000000000 : ℝ)^13
        have hw : |(3417231511/5000000000 : ℝ)|=(3417231511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203819977/1250000000 : ℝ)|^17 ≤ (9332087616541/100000000000000 : ℝ)^13
        have hw : |(-203819977/1250000000 : ℝ)|=(203819977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2696027079/10000000000 : ℝ)*x 0 + (3827682811/10000000000 : ℝ)*x 1 + (6198579139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696027079/10000000000 : ℝ)^17 ≤ (281437851507/1562500000000 : ℝ)^13 := by
    have hnat : (2696027079 : ℕ)^17*1562500000000^13 ≤ 281437851507^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696027079 10000000000 281437851507 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3827682811/10000000000 : ℝ)^17 ≤ (28484495989597/100000000000000 : ℝ)^13 := by
    have hnat : (3827682811 : ℕ)^17*100000000000000^13 ≤ 28484495989597^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3827682811 10000000000 28484495989597 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6198579139/10000000000 : ℝ)^17 ≤ (53503481504009/100000000000000 : ℝ)^13 := by
    have hnat : (6198579139 : ℕ)^17*100000000000000^13 ≤ 53503481504009^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6198579139 10000000000 53503481504009 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696027079/10000000000 : ℝ), (3827682811/10000000000 : ℝ), (6198579139/10000000000 : ℝ)] ![(281437851507/1562500000000 : ℝ), (28484495989597/100000000000000 : ℝ), (53503481504009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696027079/10000000000 : ℝ)|^17 ≤ (281437851507/1562500000000 : ℝ)^13
        have hw : |(2696027079/10000000000 : ℝ)|=(2696027079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3827682811/10000000000 : ℝ)|^17 ≤ (28484495989597/100000000000000 : ℝ)^13
        have hw : |(3827682811/10000000000 : ℝ)|=(3827682811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6198579139/10000000000 : ℝ)|^17 ≤ (53503481504009/100000000000000 : ℝ)^13
        have hw : |(6198579139/10000000000 : ℝ)|=(6198579139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-461877261/2500000000 : ℝ)*x 0 + (5671541579/10000000000 : ℝ)*x 1 + (5092617987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461877261/2500000000 : ℝ)^17 ≤ (2747014247349/25000000000000 : ℝ)^13 := by
    have hnat : (461877261 : ℕ)^17*25000000000000^13 ≤ 2747014247349^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461877261 2500000000 2747014247349 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671541579/10000000000 : ℝ)^17 ≤ (47633977769041/100000000000000 : ℝ)^13 := by
    have hnat : (5671541579 : ℕ)^17*100000000000000^13 ≤ 47633977769041^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671541579 10000000000 47633977769041 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5092617987/10000000000 : ℝ)^17 ≤ (20688982612563/50000000000000 : ℝ)^13 := by
    have hnat : (5092617987 : ℕ)^17*50000000000000^13 ≤ 20688982612563^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092617987 10000000000 20688982612563 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-461877261/2500000000 : ℝ), (5671541579/10000000000 : ℝ), (5092617987/10000000000 : ℝ)] ![(2747014247349/25000000000000 : ℝ), (47633977769041/100000000000000 : ℝ), (20688982612563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-461877261/2500000000 : ℝ)|^17 ≤ (2747014247349/25000000000000 : ℝ)^13
        have hw : |(-461877261/2500000000 : ℝ)|=(461877261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671541579/10000000000 : ℝ)|^17 ≤ (47633977769041/100000000000000 : ℝ)^13
        have hw : |(5671541579/10000000000 : ℝ)|=(5671541579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5092617987/10000000000 : ℝ)|^17 ≤ (20688982612563/50000000000000 : ℝ)^13
        have hw : |(5092617987/10000000000 : ℝ)|=(5092617987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3869330197/5000000000 : ℝ)*x 0 + (-78704971/10000000000 : ℝ)*x 1 + (3809303089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3869330197/5000000000 : ℝ)^17 ≤ (71516970274503/100000000000000 : ℝ)^13 := by
    have hnat : (3869330197 : ℕ)^17*100000000000000^13 ≤ 71516970274503^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3869330197 5000000000 71516970274503 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78704971/10000000000 : ℝ)^17 ≤ (177263048337/100000000000000 : ℝ)^13 := by
    have hnat : (78704971 : ℕ)^17*100000000000000^13 ≤ 177263048337^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78704971 10000000000 177263048337 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3809303089/10000000000 : ℝ)^17 ≤ (14152883335321/50000000000000 : ℝ)^13 := by
    have hnat : (3809303089 : ℕ)^17*50000000000000^13 ≤ 14152883335321^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3809303089 10000000000 14152883335321 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3869330197/5000000000 : ℝ), (-78704971/10000000000 : ℝ), (3809303089/10000000000 : ℝ)] ![(71516970274503/100000000000000 : ℝ), (177263048337/100000000000000 : ℝ), (14152883335321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3869330197/5000000000 : ℝ)|^17 ≤ (71516970274503/100000000000000 : ℝ)^13
        have hw : |(3869330197/5000000000 : ℝ)|=(3869330197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78704971/10000000000 : ℝ)|^17 ≤ (177263048337/100000000000000 : ℝ)^13
        have hw : |(-78704971/10000000000 : ℝ)|=(78704971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3809303089/10000000000 : ℝ)|^17 ≤ (14152883335321/50000000000000 : ℝ)^13
        have hw : |(3809303089/10000000000 : ℝ)|=(3809303089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1603945681/5000000000 : ℝ)*x 0 + (1705702609/2500000000 : ℝ)*x 1 + (-159284049/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1603945681/5000000000 : ℝ)^17 ≤ (22609306293019/100000000000000 : ℝ)^13 := by
    have hnat : (1603945681 : ℕ)^17*100000000000000^13 ≤ 22609306293019^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603945681 5000000000 22609306293019 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705702609/2500000000 : ℝ)^17 ≤ (12131236988101/20000000000000 : ℝ)^13 := by
    have hnat : (1705702609 : ℕ)^17*20000000000000^13 ≤ 12131236988101^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705702609 2500000000 12131236988101 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159284049/625000000 : ℝ)^17 ≤ (167345087487/1000000000000 : ℝ)^13 := by
    have hnat : (159284049 : ℕ)^17*1000000000000^13 ≤ 167345087487^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159284049 625000000 167345087487 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1603945681/5000000000 : ℝ), (1705702609/2500000000 : ℝ), (-159284049/625000000 : ℝ)] ![(22609306293019/100000000000000 : ℝ), (12131236988101/20000000000000 : ℝ), (167345087487/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1603945681/5000000000 : ℝ)|^17 ≤ (22609306293019/100000000000000 : ℝ)^13
        have hw : |(1603945681/5000000000 : ℝ)|=(1603945681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1705702609/2500000000 : ℝ)|^17 ≤ (12131236988101/20000000000000 : ℝ)^13
        have hw : |(1705702609/2500000000 : ℝ)|=(1705702609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-159284049/625000000 : ℝ)|^17 ≤ (167345087487/1000000000000 : ℝ)^13
        have hw : |(-159284049/625000000 : ℝ)|=(159284049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s2_s2_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4107437147/10000000000 : ℝ)*x 0 + (4573526379/10000000000 : ℝ)*x 1 + (1066216347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4107437147/10000000000 : ℝ)^17 ≤ (31237025569691/100000000000000 : ℝ)^13 := by
    have hnat : (4107437147 : ℕ)^17*100000000000000^13 ≤ 31237025569691^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4107437147 10000000000 31237025569691 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4573526379/10000000000 : ℝ)^17 ≤ (35951175277007/100000000000000 : ℝ)^13 := by
    have hnat : (4573526379 : ℕ)^17*100000000000000^13 ≤ 35951175277007^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573526379 10000000000 35951175277007 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066216347/2500000000 : ℝ)^17 ≤ (32811799146791/100000000000000 : ℝ)^13 := by
    have hnat : (1066216347 : ℕ)^17*100000000000000^13 ≤ 32811799146791^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066216347 2500000000 32811799146791 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4107437147/10000000000 : ℝ), (4573526379/10000000000 : ℝ), (1066216347/2500000000 : ℝ)] ![(31237025569691/100000000000000 : ℝ), (35951175277007/100000000000000 : ℝ), (32811799146791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4107437147/10000000000 : ℝ)|^17 ≤ (31237025569691/100000000000000 : ℝ)^13
        have hw : |(4107437147/10000000000 : ℝ)|=(4107437147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4573526379/10000000000 : ℝ)|^17 ≤ (35951175277007/100000000000000 : ℝ)^13
        have hw : |(4573526379/10000000000 : ℝ)|=(4573526379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1066216347/2500000000 : ℝ)|^17 ≤ (32811799146791/100000000000000 : ℝ)^13
        have hw : |(1066216347/2500000000 : ℝ)|=(1066216347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307083_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((31497/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31497/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((7899/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(7899/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71517/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16281/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16281/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((34571/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(34571/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35849/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (31497/50000 : ℝ) ^ (135/32 : ℝ) ≤ (3558225355213403581/25000000000000000000 : ℝ) := by
    have hpowers : (31497/50000 : ℝ)^135 ≤ (3558225355213403581/25000000000000000000 : ℝ)^32 := by
      have hnat : (31497 : ℕ)^135*25000000000000000000^32 ≤ 3558225355213403581^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31497 50000 3558225355213403581 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31497/50000 : ℝ)) (X := (3558225355213403581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (28558225355213403581/25000000000000000000 : ℝ) ≤ (258011263361961/250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (28558225355213403581/25000000000000000000 : ℝ)^32 ≤ (258011263361961/250000000000000 : ℝ)^135 := by
      have hnat : (28558225355213403581 : ℕ)^32*250000000000000^135 ≤ 258011263361961^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28558225355213403581 25000000000000000000 258011263361961 250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (258011263361961/250000000000000 : ℝ)) (X := (28558225355213403581/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (16058225355213403581/12500000000000000000 : ℝ) ≤ (42446967264323/40000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (16058225355213403581/12500000000000000000 : ℝ)^32 ≤ (42446967264323/40000000000000 : ℝ)^135 := by
      have hnat : (16058225355213403581 : ℕ)^32*40000000000000^135 ≤ 42446967264323^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16058225355213403581 12500000000000000000 42446967264323 40000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (42446967264323/40000000000000 : ℝ)) (X := (16058225355213403581/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8011263361961/157485000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(29129128160231/629940000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (31497/50000 : ℝ)) (alpha := (8011263361961/157485000000000 : ℝ)) (beta := (29129128160231/629940000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (31497/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8011263361961/157485000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(29129128160231/629940000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (7899/12500 : ℝ) ^ (135/32 : ℝ) ≤ (2884517867806419739/20000000000000000000 : ℝ) := by
    have hpowers : (7899/12500 : ℝ)^135 ≤ (2884517867806419739/20000000000000000000 : ℝ)^32 := by
      have hnat : (7899 : ℕ)^135*20000000000000000000^32 ≤ 2884517867806419739^32*12500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7899 12500 2884517867806419739 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7899/12500 : ℝ)) (X := (2884517867806419739/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (22884517867806419739/20000000000000000000 : ℝ) ≤ (10324510182678439/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (22884517867806419739/20000000000000000000 : ℝ)^32 ≤ (10324510182678439/10000000000000000 : ℝ)^135 := by
      have hnat : (22884517867806419739 : ℕ)^32*10000000000000000^135 ≤ 10324510182678439^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22884517867806419739 20000000000000000000 10324510182678439 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10324510182678439/10000000000000000 : ℝ)) (X := (22884517867806419739/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (12884517867806419739/10000000000000000000 : ℝ) ≤ (5309580843308431/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (12884517867806419739/10000000000000000000 : ℝ)^32 ≤ (5309580843308431/5000000000000000 : ℝ)^135 := by
      have hnat : (12884517867806419739 : ℕ)^32*5000000000000000^135 ≤ 5309580843308431^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12884517867806419739 10000000000000000000 5309580843308431 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5309580843308431/5000000000000000 : ℝ)) (X := (12884517867806419739/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(108170060892813/2106400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(294651503938423/6319200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (7899/12500 : ℝ)) (alpha := (108170060892813/2106400000000000 : ℝ)) (beta := (294651503938423/6319200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7899/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(108170060892813/2106400000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(294651503938423/6319200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (71517/100000 : ℝ) ^ (135/32 : ℝ) ≤ (4862047315556978593/20000000000000000000 : ℝ) := by
    have hpowers : (71517/100000 : ℝ)^135 ≤ (4862047315556978593/20000000000000000000 : ℝ)^32 := by
      have hnat : (71517 : ℕ)^135*20000000000000000000^32 ≤ 4862047315556978593^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71517 100000 4862047315556978593 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71517/100000 : ℝ)) (X := (4862047315556978593/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (24862047315556978593/20000000000000000000 : ℝ) ≤ (5264675870783863/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (24862047315556978593/20000000000000000000 : ℝ)^32 ≤ (5264675870783863/5000000000000000 : ℝ)^135 := by
      have hnat : (24862047315556978593 : ℕ)^32*5000000000000000^135 ≤ 5264675870783863^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24862047315556978593 20000000000000000000 5264675870783863 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5264675870783863/5000000000000000 : ℝ)) (X := (24862047315556978593/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (14862047315556978593/10000000000000000000 : ℝ) ≤ (2196944099249497/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (14862047315556978593/10000000000000000000 : ℝ)^32 ≤ (2196944099249497/2000000000000000 : ℝ)^135 := by
      have hnat : (14862047315556978593 : ℕ)^32*2000000000000000^135 ≤ 2196944099249497^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14862047315556978593 10000000000000000000 2196944099249497 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2196944099249497/2000000000000000 : ℝ)) (X := (14862047315556978593/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(264675870783863/3575850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4896438222363/76900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (71517/100000 : ℝ)) (alpha := (264675870783863/3575850000000000 : ℝ)) (beta := (4896438222363/76900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (71517/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(264675870783863/3575850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4896438222363/76900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1212893859/5000000000 : ℝ)*X 0 0+(2495254963/5000000000 : ℝ)*X 0 1+(1067803303/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((6863325449/10000000000 : ℝ)*X 1 0+(-499839427/5000000000 : ℝ)*X 1 1+(2188798949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((3764103517/10000000000 : ℝ)*X 2 0+(6377269001/10000000000 : ℝ)*X 2 1+(-2533252203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1223500907/5000000000 : ℝ)*X 0 0+(2479226153/5000000000 : ℝ)*X 0 1+(214148539/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((806801381/1250000000 : ℝ)*X 1 0+(-16365309/5000000000 : ℝ)*X 1 1+(661794387/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((196464549/625000000 : ℝ)*X 2 0+(7457910461/10000000000 : ℝ)*X 2 1+(-339593279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((370496301/1250000000 : ℝ)*X 0 0+(4834960127/10000000000 : ℝ)*X 0 1+(5052305937/10000000000 : ℝ)*X 0 2+(370496301/1250000000 : ℝ)*X 1 0+(4834960127/10000000000 : ℝ)*X 1 1+(5052305937/10000000000 : ℝ)*X 1 2+(370496301/1250000000 : ℝ)*X 2 0+(4834960127/10000000000 : ℝ)*X 2 1+(5052305937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1430840307/10000000000 : ℝ)*X 0 0+(952972723/2500000000 : ℝ)*X 0 1+(7091848997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4031287097/5000000000 : ℝ)*X 1 0+(-351408241/5000000000 : ℝ)*X 1 1+(3080103037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3969889969/10000000000 : ℝ)*X 2 0+(3417231511/5000000000 : ℝ)*X 2 1+(-203819977/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2696027079/10000000000 : ℝ)*X 0 0+(3827682811/10000000000 : ℝ)*X 0 1+(6198579139/10000000000 : ℝ)*X 0 2+(2696027079/10000000000 : ℝ)*X 1 0+(3827682811/10000000000 : ℝ)*X 1 1+(6198579139/10000000000 : ℝ)*X 1 2+(2696027079/10000000000 : ℝ)*X 2 0+(3827682811/10000000000 : ℝ)*X 2 1+(6198579139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-461877261/2500000000 : ℝ)*X 0 0+(5671541579/10000000000 : ℝ)*X 0 1+(5092617987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3869330197/5000000000 : ℝ)*X 1 0+(-78704971/10000000000 : ℝ)*X 1 1+(3809303089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1603945681/5000000000 : ℝ)*X 2 0+(1705702609/2500000000 : ℝ)*X 2 1+(-159284049/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4107437147/10000000000 : ℝ)*X 0 0+(4573526379/10000000000 : ℝ)*X 0 1+(1066216347/2500000000 : ℝ)*X 0 2+(4107437147/10000000000 : ℝ)*X 1 0+(4573526379/10000000000 : ℝ)*X 1 1+(1066216347/2500000000 : ℝ)*X 1 2+(4107437147/10000000000 : ℝ)*X 2 0+(4573526379/10000000000 : ℝ)*X 2 1+(1066216347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((16281/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16281/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1603790390215151307061513/391071345312500000000000000000 : ℝ) := by norm_num
    linear_combination (83659/25000000000 : ℝ)*(base19) + (2185979883/200000000000 : ℝ)*(base40) + (924140841557/1000000000000 : ℝ)*(base49) + (11883389301/40000000000 : ℝ)*(base60) + (3716975836387/1000000000000 : ℝ)*(major_s2_0) + (3716975836387/1000000000000 : ℝ)*(major_s2_1) + (3716975836387/1000000000000 : ℝ)*(major_s2_2) + (911051151/1000000000000 : ℝ)*(sp_s2_0) + (145451/31250000000 : ℝ)*(sp_s2_1) + (504190148739/100000000000 : ℝ)*(sp_s2_7) + (20171218151/4000000000 : ℝ)*(sp_s2_8) + (5042812538541/1000000000000 : ℝ)*(sp_s2_9) + (1195560520727/500000000000 : ℝ)*(sp_s2_13) + (3345153/200000000000 : ℝ)*(sp_s2_20) + (2391137767219/1000000000000 : ℝ)*(f.failure) + (5042812538541/1000000000000 : ℝ)*(f.sum) + (15339714442722508297/50214469600000000000000000000000 : ℝ)*base62 + (62025126244571/76900000000000000000000000 : ℝ)*base65 + (1420213145747911/2106400000000000000000000000 : ℝ)*base67 + (51747620734247/1787925000000000000000000000 : ℝ)*base68 + (1803252373777288867/2422119300000000000000000000000 : ℝ)*base71 + (281936844501589/629940000000000000000000000 : ℝ)*base72 + (3231882941595179/6319200000000000000000000000 : ℝ)*base75 + (90947477635309/78742500000000000000000000 : ℝ)*base77 + (32057955532058858393/66345280800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (5111/12500000000000000 : ℝ)*base86 + (5111/12500000000000000 : ℝ)*base88 + (5111/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((34571/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(34571/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (761043369267553846080363495183/65900214541300000000000000000000000 : ℝ) := by norm_num
    linear_combination (15759509/1000000000000 : ℝ)*(base21) + (741739790871/1000000000000 : ℝ)*(base40) + (779641733923/1000000000000 : ℝ)*(base49) + (624335372257/1000000000000 : ℝ)*(base60) + (1615239159819/500000000000 : ℝ)*(major_s2_0) + (1615239159819/500000000000 : ℝ)*(major_s2_1) + (1615239159819/500000000000 : ℝ)*(major_s2_2) + (8843453/500000000000 : ℝ)*(sp_s2_1) + (30937/100000000000 : ℝ)*(sp_s2_2) + (876555963801/200000000000 : ℝ)*(sp_s2_14) + (68479833611/15625000000 : ℝ)*(sp_s2_15) + (4382763750127/1000000000000 : ℝ)*(sp_s2_16) + (2078172970793/1000000000000 : ℝ)*(sp_s2_20) + (10556199/200000000000 : ℝ)*(sp_s2_22) + (2078172970793/1000000000000 : ℝ)*(f.failure) + (876555963801/200000000000 : ℝ)*(f.sum) + (20810491946367621969/25107234800000000000000000000000 : ℝ)*base62 + (8791508722831/19225000000000000000000000 : ℝ)*base65 + (99716238153007/1053200000000000000000000000 : ℝ)*base67 + (37960133871967/1191950000000000000000000000 : ℝ)*base68 + (18587527974300187/403686550000000000000000000000 : ℝ)*base70 + (30088754704281/104990000000000000000000000 : ℝ)*base73 + (865712939488479/1053200000000000000000000000 : ℝ)*base74 + (58064653737801/104990000000000000000000000 : ℝ)*base76 + (1930753342977908013/11057546800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (3783/12500000000000000 : ℝ)*base87 + (3783/12500000000000000 : ℝ)*base89 + (3783/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35849/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64885505218315224192505430621/16475053635325000000000000000000000 : ℝ) := by norm_num
    linear_combination (92639/50000000000 : ℝ)*(base11) + (703802234321/1000000000000 : ℝ)*(base40) + (132188523477/125000000000 : ℝ)*(base49) + (494483/500000000000 : ℝ)*(base50) + (2082317782147/500000000000 : ℝ)*(major_s2_0) + (2082317782147/500000000000 : ℝ)*(major_s2_1) + (2082317782147/500000000000 : ℝ)*(major_s2_2) + (1698519/250000000000 : ℝ)*(sp_s2_2) + (15393397/1000000000000 : ℝ)*(sp_s2_15) + (16396697/1000000000000 : ℝ)*(sp_s2_16) + (1130029964853/200000000000 : ℝ)*(sp_s2_21) + (11035422429/1953125000 : ℝ)*(sp_s2_22) + (44141628799/7812500000 : ℝ)*(sp_s2_23) + (267911813873/100000000000 : ℝ)*(sp_s2_27) + (267911813873/100000000000 : ℝ)*(f.failure) + (1130030335409/200000000000 : ℝ)*(f.sum) + (11870508821827749783/25107234800000000000000000000000 : ℝ)*base63 + (7182349241159/9612500000000000000000000 : ℝ)*base65 + (625231067360111/1053200000000000000000000000 : ℝ)*base67 + (1081213919844161/1787925000000000000000000000 : ℝ)*base69 + (501552070570798657/1211059650000000000000000000000 : ℝ)*base71 + (5968708310113/15748500000000000000000000 : ℝ)*base73 + (2542732897560179/3159600000000000000000000000 : ℝ)*base75 + (65940380220521/78742500000000000000000000 : ℝ)*base77 + (2749202621171598727/33172640400000000000000000000000 : ℝ)*base79 + (1237/1250000000000000 : ℝ)*base86 + (1237/1250000000000000 : ℝ)*base88 + (1237/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((31497/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31497/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((7899/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(7899/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71517/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16281/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16281/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((34571/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(34571/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35849/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35849/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307083_s2 p hpa hpb X hX hprev1

#print axioms solution
