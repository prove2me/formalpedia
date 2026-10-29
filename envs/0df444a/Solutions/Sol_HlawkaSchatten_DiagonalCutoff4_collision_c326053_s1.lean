-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c326053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:10:45.41098+00:00
-- url     : https://prove2.me/submissions/f90f3803-67a8-4b69-a3aa-960544be8486

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
theorem collision_support_c326053_s1_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-15649883/80000000 : ℝ)*x 0 + (2502122033/5000000000 : ℝ)*x 1 + (314701077/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15649883/80000000 : ℝ)^89 ≤ (6840473264057/50000000000000 : ℝ)^73 := by
    have hnat : (15649883 : ℕ)^89*50000000000000^73 ≤ 6840473264057^73*80000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15649883 80000000 6840473264057 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502122033/5000000000 : ℝ)^89 ≤ (537464867741/1250000000000 : ℝ)^73 := by
    have hnat : (2502122033 : ℕ)^89*1250000000000^73 ≤ 537464867741^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502122033 5000000000 537464867741 1250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314701077/625000000 : ℝ)^89 ≤ (43321864035589/100000000000000 : ℝ)^73 := by
    have hnat : (314701077 : ℕ)^89*100000000000000^73 ≤ 43321864035589^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314701077 625000000 43321864035589 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15649883/80000000 : ℝ), (2502122033/5000000000 : ℝ), (314701077/625000000 : ℝ)] ![(6840473264057/50000000000000 : ℝ), (537464867741/1250000000000 : ℝ), (43321864035589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15649883/80000000 : ℝ)|^89 ≤ (6840473264057/50000000000000 : ℝ)^73
        have hw : |(-15649883/80000000 : ℝ)|=(15649883/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502122033/5000000000 : ℝ)|^89 ≤ (537464867741/1250000000000 : ℝ)^73
        have hw : |(2502122033/5000000000 : ℝ)|=(2502122033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314701077/625000000 : ℝ)|^89 ≤ (43321864035589/100000000000000 : ℝ)^73
        have hw : |(314701077/625000000 : ℝ)|=(314701077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (888746291/2000000000 : ℝ)*x 0 + (-174779477/1250000000 : ℝ)*x 1 + (300324227/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888746291/2000000000 : ℝ)^89 ≤ (18599953118257/50000000000000 : ℝ)^73 := by
    have hnat : (888746291 : ℕ)^89*50000000000000^73 ≤ 18599953118257^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888746291 2000000000 18599953118257 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174779477/1250000000 : ℝ)^89 ≤ (9084695558729/100000000000000 : ℝ)^73 := by
    have hnat : (174779477 : ℕ)^89*100000000000000^73 ≤ 9084695558729^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174779477 1250000000 9084695558729 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300324227/500000000 : ℝ)^89 ≤ (53715398184519/100000000000000 : ℝ)^73 := by
    have hnat : (300324227 : ℕ)^89*100000000000000^73 ≤ 53715398184519^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300324227 500000000 53715398184519 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(888746291/2000000000 : ℝ), (-174779477/1250000000 : ℝ), (300324227/500000000 : ℝ)] ![(18599953118257/50000000000000 : ℝ), (9084695558729/100000000000000 : ℝ), (53715398184519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(888746291/2000000000 : ℝ)|^89 ≤ (18599953118257/50000000000000 : ℝ)^73
        have hw : |(888746291/2000000000 : ℝ)|=(888746291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174779477/1250000000 : ℝ)|^89 ≤ (9084695558729/100000000000000 : ℝ)^73
        have hw : |(-174779477/1250000000 : ℝ)|=(174779477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300324227/500000000 : ℝ)|^89 ≤ (53715398184519/100000000000000 : ℝ)^73
        have hw : |(300324227/500000000 : ℝ)|=(300324227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4461487547/10000000000 : ℝ)*x 0 + (6003828571/10000000000 : ℝ)*x 1 + (-275794901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4461487547/10000000000 : ℝ)^89 ≤ (37381206530229/100000000000000 : ℝ)^73 := by
    have hnat : (4461487547 : ℕ)^89*100000000000000^73 ≤ 37381206530229^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4461487547 10000000000 37381206530229 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6003828571/10000000000 : ℝ)^89 ≤ (53686441586587/100000000000000 : ℝ)^73 := by
    have hnat : (6003828571 : ℕ)^89*100000000000000^73 ≤ 53686441586587^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003828571 10000000000 53686441586587 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275794901/2000000000 : ℝ)^89 ≤ (8932351874403/100000000000000 : ℝ)^73 := by
    have hnat : (275794901 : ℕ)^89*100000000000000^73 ≤ 8932351874403^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275794901 2000000000 8932351874403 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4461487547/10000000000 : ℝ), (6003828571/10000000000 : ℝ), (-275794901/2000000000 : ℝ)] ![(37381206530229/100000000000000 : ℝ), (53686441586587/100000000000000 : ℝ), (8932351874403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4461487547/10000000000 : ℝ)|^89 ≤ (37381206530229/100000000000000 : ℝ)^73
        have hw : |(4461487547/10000000000 : ℝ)|=(4461487547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6003828571/10000000000 : ℝ)|^89 ≤ (53686441586587/100000000000000 : ℝ)^73
        have hw : |(6003828571/10000000000 : ℝ)|=(6003828571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275794901/2000000000 : ℝ)|^89 ≤ (8932351874403/100000000000000 : ℝ)^73
        have hw : |(-275794901/2000000000 : ℝ)|=(275794901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7170449463/10000000000 : ℝ)*x 0 + (36293601/156250000 : ℝ)*x 1 + (1138854401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7170449463/10000000000 : ℝ)^89 ≤ (13332614048509/20000000000000 : ℝ)^73 := by
    have hnat : (7170449463 : ℕ)^89*20000000000000^73 ≤ 13332614048509^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7170449463 10000000000 13332614048509 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36293601/156250000 : ℝ)^89 ≤ (8433800700297/50000000000000 : ℝ)^73 := by
    have hnat : (36293601 : ℕ)^89*50000000000000^73 ≤ 8433800700297^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36293601 156250000 8433800700297 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138854401/5000000000 : ℝ)^89 ≤ (16469328334517/100000000000000 : ℝ)^73 := by
    have hnat : (1138854401 : ℕ)^89*100000000000000^73 ≤ 16469328334517^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138854401 5000000000 16469328334517 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7170449463/10000000000 : ℝ), (36293601/156250000 : ℝ), (1138854401/5000000000 : ℝ)] ![(13332614048509/20000000000000 : ℝ), (8433800700297/50000000000000 : ℝ), (16469328334517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7170449463/10000000000 : ℝ)|^89 ≤ (13332614048509/20000000000000 : ℝ)^73
        have hw : |(7170449463/10000000000 : ℝ)|=(7170449463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36293601/156250000 : ℝ)|^89 ≤ (8433800700297/50000000000000 : ℝ)^73
        have hw : |(36293601/156250000 : ℝ)|=(36293601/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1138854401/5000000000 : ℝ)|^89 ≤ (16469328334517/100000000000000 : ℝ)^73
        have hw : |(1138854401/5000000000 : ℝ)|=(1138854401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1921862269/10000000000 : ℝ)*x 0 + (1058702851/2500000000 : ℝ)*x 1 + (5805557891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1921862269/10000000000 : ℝ)^89 ≤ (13388436999559/100000000000000 : ℝ)^73 := by
    have hnat : (1921862269 : ℕ)^89*100000000000000^73 ≤ 13388436999559^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921862269 10000000000 13388436999559 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058702851/2500000000 : ℝ)^89 ≤ (17539381972229/50000000000000 : ℝ)^73 := by
    have hnat : (1058702851 : ℕ)^89*50000000000000^73 ≤ 17539381972229^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058702851 2500000000 17539381972229 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5805557891/10000000000 : ℝ)^89 ≤ (51532799040767/100000000000000 : ℝ)^73 := by
    have hnat : (5805557891 : ℕ)^89*100000000000000^73 ≤ 51532799040767^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5805557891 10000000000 51532799040767 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1921862269/10000000000 : ℝ), (1058702851/2500000000 : ℝ), (5805557891/10000000000 : ℝ)] ![(13388436999559/100000000000000 : ℝ), (17539381972229/50000000000000 : ℝ), (51532799040767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1921862269/10000000000 : ℝ)|^89 ≤ (13388436999559/100000000000000 : ℝ)^73
        have hw : |(-1921862269/10000000000 : ℝ)|=(1921862269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058702851/2500000000 : ℝ)|^89 ≤ (17539381972229/50000000000000 : ℝ)^73
        have hw : |(1058702851/2500000000 : ℝ)|=(1058702851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5805557891/10000000000 : ℝ)|^89 ≤ (51532799040767/100000000000000 : ℝ)^73
        have hw : |(5805557891/10000000000 : ℝ)|=(5805557891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4231130717/10000000000 : ℝ)*x 0 + (-236619789/2000000000 : ℝ)*x 1 + (6355800561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4231130717/10000000000 : ℝ)^89 ≤ (27376247121/78125000000 : ℝ)^73 := by
    have hnat : (4231130717 : ℕ)^89*78125000000^73 ≤ 27376247121^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231130717 10000000000 27376247121 78125000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236619789/2000000000 : ℝ)^89 ≤ (1482100309627/20000000000000 : ℝ)^73 := by
    have hnat : (236619789 : ℕ)^89*20000000000000^73 ≤ 1482100309627^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236619789 2000000000 1482100309627 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6355800561/10000000000 : ℝ)^89 ≤ (14386975530703/25000000000000 : ℝ)^73 := by
    have hnat : (6355800561 : ℕ)^89*25000000000000^73 ≤ 14386975530703^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6355800561 10000000000 14386975530703 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4231130717/10000000000 : ℝ), (-236619789/2000000000 : ℝ), (6355800561/10000000000 : ℝ)] ![(27376247121/78125000000 : ℝ), (1482100309627/20000000000000 : ℝ), (14386975530703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4231130717/10000000000 : ℝ)|^89 ≤ (27376247121/78125000000 : ℝ)^73
        have hw : |(4231130717/10000000000 : ℝ)|=(4231130717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236619789/2000000000 : ℝ)|^89 ≤ (1482100309627/20000000000000 : ℝ)^73
        have hw : |(-236619789/2000000000 : ℝ)|=(236619789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6355800561/10000000000 : ℝ)|^89 ≤ (14386975530703/25000000000000 : ℝ)^73
        have hw : |(6355800561/10000000000 : ℝ)|=(6355800561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4248966939/10000000000 : ℝ)*x 0 + (418420299/625000000 : ℝ)*x 1 + (-79320487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248966939/10000000000 : ℝ)^89 ≤ (1408870907183/4000000000000 : ℝ)^73 := by
    have hnat : (4248966939 : ℕ)^89*4000000000000^73 ≤ 1408870907183^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248966939 10000000000 1408870907183 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (418420299/625000000 : ℝ)^89 ≤ (61310825233987/100000000000000 : ℝ)^73 := by
    have hnat : (418420299 : ℕ)^89*100000000000000^73 ≤ 61310825233987^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418420299 625000000 61310825233987 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79320487/1250000000 : ℝ)^89 ≤ (346740207501/10000000000000 : ℝ)^73 := by
    have hnat : (79320487 : ℕ)^89*10000000000000^73 ≤ 346740207501^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79320487 1250000000 346740207501 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248966939/10000000000 : ℝ), (418420299/625000000 : ℝ), (-79320487/1250000000 : ℝ)] ![(1408870907183/4000000000000 : ℝ), (61310825233987/100000000000000 : ℝ), (346740207501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248966939/10000000000 : ℝ)|^89 ≤ (1408870907183/4000000000000 : ℝ)^73
        have hw : |(4248966939/10000000000 : ℝ)|=(4248966939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(418420299/625000000 : ℝ)|^89 ≤ (61310825233987/100000000000000 : ℝ)^73
        have hw : |(418420299/625000000 : ℝ)|=(418420299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79320487/1250000000 : ℝ)|^89 ≤ (346740207501/10000000000000 : ℝ)^73
        have hw : |(-79320487/1250000000 : ℝ)|=(79320487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7038301841/10000000000 : ℝ)*x 0 + (67947459/200000000 : ℝ)*x 1 + (1261900647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7038301841/10000000000 : ℝ)^89 ≤ (32584134994777/50000000000000 : ℝ)^73 := by
    have hnat : (7038301841 : ℕ)^89*50000000000000^73 ≤ 32584134994777^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7038301841 10000000000 32584134994777 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67947459/200000000 : ℝ)^89 ≤ (2681514166797/10000000000000 : ℝ)^73 := by
    have hnat : (67947459 : ℕ)^89*10000000000000^73 ≤ 2681514166797^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67947459 200000000 2681514166797 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1261900647/10000000000 : ℝ)^89 ≤ (4008294166417/50000000000000 : ℝ)^73 := by
    have hnat : (1261900647 : ℕ)^89*50000000000000^73 ≤ 4008294166417^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261900647 10000000000 4008294166417 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7038301841/10000000000 : ℝ), (67947459/200000000 : ℝ), (1261900647/10000000000 : ℝ)] ![(32584134994777/50000000000000 : ℝ), (2681514166797/10000000000000 : ℝ), (4008294166417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7038301841/10000000000 : ℝ)|^89 ≤ (32584134994777/50000000000000 : ℝ)^73
        have hw : |(7038301841/10000000000 : ℝ)|=(7038301841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67947459/200000000 : ℝ)|^89 ≤ (2681514166797/10000000000000 : ℝ)^73
        have hw : |(67947459/200000000 : ℝ)|=(67947459/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1261900647/10000000000 : ℝ)|^89 ≤ (4008294166417/50000000000000 : ℝ)^73
        have hw : |(1261900647/10000000000 : ℝ)|=(1261900647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-604273189/5000000000 : ℝ)*x 0 + (4867086699/10000000000 : ℝ)*x 1 + (5740531413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (604273189/5000000000 : ℝ)^89 ≤ (7605286094027/100000000000000 : ℝ)^73 := by
    have hnat : (604273189 : ℕ)^89*100000000000000^73 ≤ 7605286094027^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604273189 5000000000 7605286094027 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4867086699/10000000000 : ℝ)^89 ≤ (20782382040221/50000000000000 : ℝ)^73 := by
    have hnat : (4867086699 : ℕ)^89*50000000000000^73 ≤ 20782382040221^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867086699 10000000000 20782382040221 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5740531413/10000000000 : ℝ)^89 ≤ (25414974905727/50000000000000 : ℝ)^73 := by
    have hnat : (5740531413 : ℕ)^89*50000000000000^73 ≤ 25414974905727^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5740531413 10000000000 25414974905727 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-604273189/5000000000 : ℝ), (4867086699/10000000000 : ℝ), (5740531413/10000000000 : ℝ)] ![(7605286094027/100000000000000 : ℝ), (20782382040221/50000000000000 : ℝ), (25414974905727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-604273189/5000000000 : ℝ)|^89 ≤ (7605286094027/100000000000000 : ℝ)^73
        have hw : |(-604273189/5000000000 : ℝ)|=(604273189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4867086699/10000000000 : ℝ)|^89 ≤ (20782382040221/50000000000000 : ℝ)^73
        have hw : |(4867086699/10000000000 : ℝ)|=(4867086699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5740531413/10000000000 : ℝ)|^89 ≤ (25414974905727/50000000000000 : ℝ)^73
        have hw : |(5740531413/10000000000 : ℝ)|=(5740531413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4179903683/10000000000 : ℝ)*x 0 + (-243596801/2000000000 : ℝ)*x 1 + (3189187757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179903683/10000000000 : ℝ)^89 ≤ (17262521377509/50000000000000 : ℝ)^73 := by
    have hnat : (4179903683 : ℕ)^89*50000000000000^73 ≤ 17262521377509^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179903683 10000000000 17262521377509 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243596801/2000000000 : ℝ)^89 ≤ (959719400831/12500000000000 : ℝ)^73 := by
    have hnat : (243596801 : ℕ)^89*12500000000000^73 ≤ 959719400831^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243596801 2000000000 959719400831 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189187757/5000000000 : ℝ)^89 ≤ (2889860100873/5000000000000 : ℝ)^73 := by
    have hnat : (3189187757 : ℕ)^89*5000000000000^73 ≤ 2889860100873^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189187757 5000000000 2889860100873 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179903683/10000000000 : ℝ), (-243596801/2000000000 : ℝ), (3189187757/5000000000 : ℝ)] ![(17262521377509/50000000000000 : ℝ), (959719400831/12500000000000 : ℝ), (2889860100873/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179903683/10000000000 : ℝ)|^89 ≤ (17262521377509/50000000000000 : ℝ)^73
        have hw : |(4179903683/10000000000 : ℝ)|=(4179903683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243596801/2000000000 : ℝ)|^89 ≤ (959719400831/12500000000000 : ℝ)^73
        have hw : |(-243596801/2000000000 : ℝ)|=(243596801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189187757/5000000000 : ℝ)|^89 ≤ (2889860100873/5000000000000 : ℝ)^73
        have hw : |(3189187757/5000000000 : ℝ)|=(3189187757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5235124601/10000000000 : ℝ)*x 0 + (229016561/400000000 : ℝ)*x 1 + (-699594751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235124601/10000000000 : ℝ)^89 ≤ (22713914725897/50000000000000 : ℝ)^73 := by
    have hnat : (5235124601 : ℕ)^89*50000000000000^73 ≤ 22713914725897^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235124601 10000000000 22713914725897 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229016561/400000000 : ℝ)^89 ≤ (6333350024751/12500000000000 : ℝ)^73 := by
    have hnat : (229016561 : ℕ)^89*12500000000000^73 ≤ 6333350024751^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229016561 400000000 6333350024751 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699594751/10000000000 : ℝ)^89 ≤ (3905370333197/100000000000000 : ℝ)^73 := by
    have hnat : (699594751 : ℕ)^89*100000000000000^73 ≤ 3905370333197^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699594751 10000000000 3905370333197 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235124601/10000000000 : ℝ), (229016561/400000000 : ℝ), (-699594751/10000000000 : ℝ)] ![(22713914725897/50000000000000 : ℝ), (6333350024751/12500000000000 : ℝ), (3905370333197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235124601/10000000000 : ℝ)|^89 ≤ (22713914725897/50000000000000 : ℝ)^73
        have hw : |(5235124601/10000000000 : ℝ)|=(5235124601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229016561/400000000 : ℝ)|^89 ≤ (6333350024751/12500000000000 : ℝ)^73
        have hw : |(229016561/400000000 : ℝ)|=(229016561/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-699594751/10000000000 : ℝ)|^89 ≤ (3905370333197/100000000000000 : ℝ)^73
        have hw : |(-699594751/10000000000 : ℝ)|=(699594751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8051142257/10000000000 : ℝ)*x 0 + (1097942633/5000000000 : ℝ)*x 1 + (1191337393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8051142257/10000000000 : ℝ)^89 ≤ (7677565456761/10000000000000 : ℝ)^73 := by
    have hnat : (8051142257 : ℕ)^89*10000000000000^73 ≤ 7677565456761^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8051142257 10000000000 7677565456761 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097942633/5000000000 : ℝ)^89 ≤ (15750883136463/100000000000000 : ℝ)^73 := by
    have hnat : (1097942633 : ℕ)^89*100000000000000^73 ≤ 15750883136463^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097942633 5000000000 15750883136463 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1191337393/10000000000 : ℝ)^89 ≤ (1868365570433/25000000000000 : ℝ)^73 := by
    have hnat : (1191337393 : ℕ)^89*25000000000000^73 ≤ 1868365570433^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191337393 10000000000 1868365570433 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8051142257/10000000000 : ℝ), (1097942633/5000000000 : ℝ), (1191337393/10000000000 : ℝ)] ![(7677565456761/10000000000000 : ℝ), (15750883136463/100000000000000 : ℝ), (1868365570433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8051142257/10000000000 : ℝ)|^89 ≤ (7677565456761/10000000000000 : ℝ)^73
        have hw : |(8051142257/10000000000 : ℝ)|=(8051142257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097942633/5000000000 : ℝ)|^89 ≤ (15750883136463/100000000000000 : ℝ)^73
        have hw : |(1097942633/5000000000 : ℝ)|=(1097942633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1191337393/10000000000 : ℝ)|^89 ≤ (1868365570433/25000000000000 : ℝ)^73
        have hw : |(1191337393/10000000000 : ℝ)|=(1191337393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104720797/10000000000 : ℝ)*x 0 + (1061709537/2000000000 : ℝ)*x 1 + (2690595371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104720797/10000000000 : ℝ)^89 ≤ (3408195185603/50000000000000 : ℝ)^73 := by
    have hnat : (1104720797 : ℕ)^89*50000000000000^73 ≤ 3408195185603^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104720797 10000000000 3408195185603 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061709537/2000000000 : ℝ)^89 ≤ (46205793112571/100000000000000 : ℝ)^73 := by
    have hnat : (1061709537 : ℕ)^89*100000000000000^73 ≤ 46205793112571^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061709537 2000000000 46205793112571 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2690595371/5000000000 : ℝ)^89 ≤ (46977816502109/100000000000000 : ℝ)^73 := by
    have hnat : (2690595371 : ℕ)^89*100000000000000^73 ≤ 46977816502109^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690595371 5000000000 46977816502109 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104720797/10000000000 : ℝ), (1061709537/2000000000 : ℝ), (2690595371/5000000000 : ℝ)] ![(3408195185603/50000000000000 : ℝ), (46205793112571/100000000000000 : ℝ), (46977816502109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104720797/10000000000 : ℝ)|^89 ≤ (3408195185603/50000000000000 : ℝ)^73
        have hw : |(-1104720797/10000000000 : ℝ)|=(1104720797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061709537/2000000000 : ℝ)|^89 ≤ (46205793112571/100000000000000 : ℝ)^73
        have hw : |(1061709537/2000000000 : ℝ)|=(1061709537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2690595371/5000000000 : ℝ)|^89 ≤ (46977816502109/100000000000000 : ℝ)^73
        have hw : |(2690595371/5000000000 : ℝ)|=(2690595371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (42568977/80000000 : ℝ)*x 0 + (-408732881/5000000000 : ℝ)*x 1 + (5564767573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42568977/80000000 : ℝ)^89 ≤ (11584816200549/25000000000000 : ℝ)^73 := by
    have hnat : (42568977 : ℕ)^89*25000000000000^73 ≤ 11584816200549^73*80000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42568977 80000000 11584816200549 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408732881/5000000000 : ℝ)^89 ≤ (1180447691711/25000000000000 : ℝ)^73 := by
    have hnat : (408732881 : ℕ)^89*25000000000000^73 ≤ 1180447691711^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408732881 5000000000 1180447691711 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5564767573/10000000000 : ℝ)^89 ≤ (12234736106861/25000000000000 : ℝ)^73 := by
    have hnat : (5564767573 : ℕ)^89*25000000000000^73 ≤ 12234736106861^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5564767573 10000000000 12234736106861 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42568977/80000000 : ℝ), (-408732881/5000000000 : ℝ), (5564767573/10000000000 : ℝ)] ![(11584816200549/25000000000000 : ℝ), (1180447691711/25000000000000 : ℝ), (12234736106861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42568977/80000000 : ℝ)|^89 ≤ (11584816200549/25000000000000 : ℝ)^73
        have hw : |(42568977/80000000 : ℝ)|=(42568977/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408732881/5000000000 : ℝ)|^89 ≤ (1180447691711/25000000000000 : ℝ)^73
        have hw : |(-408732881/5000000000 : ℝ)|=(408732881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5564767573/10000000000 : ℝ)|^89 ≤ (12234736106861/25000000000000 : ℝ)^73
        have hw : |(5564767573/10000000000 : ℝ)|=(5564767573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4151852601/10000000000 : ℝ)*x 0 + (6561299377/10000000000 : ℝ)*x 1 + (-985828767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151852601/10000000000 : ℝ)^89 ≤ (34242772810789/100000000000000 : ℝ)^73 := by
    have hnat : (4151852601 : ℕ)^89*100000000000000^73 ≤ 34242772810789^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151852601 10000000000 34242772810789 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6561299377/10000000000 : ℝ)^89 ≤ (59824357248491/100000000000000 : ℝ)^73 := by
    have hnat : (6561299377 : ℕ)^89*100000000000000^73 ≤ 59824357248491^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6561299377 10000000000 59824357248491 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985828767/10000000000 : ℝ)^89 ≤ (2966434961003/50000000000000 : ℝ)^73 := by
    have hnat : (985828767 : ℕ)^89*50000000000000^73 ≤ 2966434961003^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985828767 10000000000 2966434961003 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151852601/10000000000 : ℝ), (6561299377/10000000000 : ℝ), (-985828767/10000000000 : ℝ)] ![(34242772810789/100000000000000 : ℝ), (59824357248491/100000000000000 : ℝ), (2966434961003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151852601/10000000000 : ℝ)|^89 ≤ (34242772810789/100000000000000 : ℝ)^73
        have hw : |(4151852601/10000000000 : ℝ)|=(4151852601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6561299377/10000000000 : ℝ)|^89 ≤ (59824357248491/100000000000000 : ℝ)^73
        have hw : |(6561299377/10000000000 : ℝ)|=(6561299377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985828767/10000000000 : ℝ)|^89 ≤ (2966434961003/50000000000000 : ℝ)^73
        have hw : |(-985828767/10000000000 : ℝ)|=(985828767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326053_s1_s1_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2048631943/2500000000 : ℝ)*x 0 + (1601341353/10000000000 : ℝ)*x 1 + (1615735793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048631943/2500000000 : ℝ)^89 ≤ (39222952040791/50000000000000 : ℝ)^73 := by
    have hnat : (2048631943 : ℕ)^89*50000000000000^73 ≤ 39222952040791^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048631943 2500000000 39222952040791 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1601341353/10000000000 : ℝ)^89 ≤ (2143651714759/20000000000000 : ℝ)^73 := by
    have hnat : (1601341353 : ℕ)^89*20000000000000^73 ≤ 2143651714759^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601341353 10000000000 2143651714759 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1615735793/10000000000 : ℝ)^89 ≤ (10835837325731/100000000000000 : ℝ)^73 := by
    have hnat : (1615735793 : ℕ)^89*100000000000000^73 ≤ 10835837325731^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615735793 10000000000 10835837325731 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2048631943/2500000000 : ℝ), (1601341353/10000000000 : ℝ), (1615735793/10000000000 : ℝ)] ![(39222952040791/50000000000000 : ℝ), (2143651714759/20000000000000 : ℝ), (10835837325731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2048631943/2500000000 : ℝ)|^89 ≤ (39222952040791/50000000000000 : ℝ)^73
        have hw : |(2048631943/2500000000 : ℝ)|=(2048631943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1601341353/10000000000 : ℝ)|^89 ≤ (2143651714759/20000000000000 : ℝ)^73
        have hw : |(1601341353/10000000000 : ℝ)|=(1601341353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1615735793/10000000000 : ℝ)|^89 ≤ (10835837325731/100000000000000 : ℝ)^73
        have hw : |(1615735793/10000000000 : ℝ)|=(1615735793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326053_s1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((64883/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64883/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65107/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(65107/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3967/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3967/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33093/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33093/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31629/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31629/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (64883/100000 : ℝ) ^ (87/16 : ℝ) ≤ (2379040842927123037/25000000000000000000 : ℝ) := by
    have hpowers : (64883/100000 : ℝ)^87 ≤ (2379040842927123037/25000000000000000000 : ℝ)^16 := by
      have hnat : (64883 : ℕ)^87*25000000000000000000^16 ≤ 2379040842927123037^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64883 100000 2379040842927123037 25000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64883/100000 : ℝ)) (X := (2379040842927123037/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (27379040842927123037/25000000000000000000 : ℝ) ≤ (10168581234861951/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (27379040842927123037/25000000000000000000 : ℝ)^16 ≤ (10168581234861951/10000000000000000 : ℝ)^87 := by
      have hnat : (27379040842927123037 : ℕ)^16*10000000000000000^87 ≤ 10168581234861951^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27379040842927123037 25000000000000000000 10168581234861951 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10168581234861951/10000000000000000 : ℝ)) (X := (27379040842927123037/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (14879040842927123037/12500000000000000000 : ℝ) ≤ (10325602165316167/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (14879040842927123037/12500000000000000000 : ℝ)^16 ≤ (10325602165316167/10000000000000000 : ℝ)^87 := by
      have hnat : (14879040842927123037 : ℕ)^16*10000000000000000^87 ≤ 10325602165316167^87*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14879040842927123037 12500000000000000000 10325602165316167 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10325602165316167/10000000000000000 : ℝ)) (X := (14879040842927123037/12500000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(168581234861951/6488300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(19627616306777/811037500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (64883/100000 : ℝ)) (alpha := (168581234861951/6488300000000000 : ℝ)) (beta := (19627616306777/811037500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64883/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(168581234861951/6488300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(19627616306777/811037500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (65107/100000 : ℝ) ^ (87/16 : ℝ) ≤ (9696176979718704871/100000000000000000000 : ℝ) := by
    have hpowers : (65107/100000 : ℝ)^87 ≤ (9696176979718704871/100000000000000000000 : ℝ)^16 := by
      have hnat : (65107 : ℕ)^87*100000000000000000000^16 ≤ 9696176979718704871^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65107 100000 9696176979718704871 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65107/100000 : ℝ)) (X := (9696176979718704871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (109696176979718704871/100000000000000000000 : ℝ) ≤ (1271456633051153/1250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (109696176979718704871/100000000000000000000 : ℝ)^16 ≤ (1271456633051153/1250000000000000 : ℝ)^87 := by
      have hnat : (109696176979718704871 : ℕ)^16*1250000000000000^87 ≤ 1271456633051153^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109696176979718704871 100000000000000000000 1271456633051153 1250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1271456633051153/1250000000000000 : ℝ)) (X := (109696176979718704871/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (59696176979718704871/50000000000000000000 : ℝ) ≤ (1033133872053237/1000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (59696176979718704871/50000000000000000000 : ℝ)^16 ≤ (1033133872053237/1000000000000000 : ℝ)^87 := by
      have hnat : (59696176979718704871 : ℕ)^16*1000000000000000^87 ≤ 1033133872053237^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59696176979718704871 50000000000000000000 1033133872053237 1000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1033133872053237/1000000000000000 : ℝ)) (X := (59696176979718704871/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(21456633051153/813837500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(79842828061573/3255350000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (65107/100000 : ℝ)) (alpha := (21456633051153/813837500000000 : ℝ)) (beta := (79842828061573/3255350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (65107/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(21456633051153/813837500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(79842828061573/3255350000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3967/6250 : ℝ) ^ (87/16 : ℝ) ≤ (8443852159113924597/100000000000000000000 : ℝ) := by
    have hpowers : (3967/6250 : ℝ)^87 ≤ (8443852159113924597/100000000000000000000 : ℝ)^16 := by
      have hnat : (3967 : ℕ)^87*100000000000000000000^16 ≤ 8443852159113924597^16*6250^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3967 6250 8443852159113924597 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3967/6250 : ℝ)) (X := (8443852159113924597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (108443852159113924597/100000000000000000000 : ℝ) ≤ (10150196993095903/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (108443852159113924597/100000000000000000000 : ℝ)^16 ≤ (10150196993095903/10000000000000000 : ℝ)^87 := by
      have hnat : (108443852159113924597 : ℕ)^16*10000000000000000^87 ≤ 10150196993095903^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108443852159113924597 100000000000000000000 10150196993095903 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10150196993095903/10000000000000000 : ℝ)) (X := (108443852159113924597/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (58443852159113924597/50000000000000000000 : ℝ) ≤ (2572783498794789/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (58443852159113924597/50000000000000000000 : ℝ)^16 ≤ (2572783498794789/2500000000000000 : ℝ)^87 := by
      have hnat : (58443852159113924597 : ℕ)^16*2500000000000000^87 ≤ 2572783498794789^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58443852159113924597 50000000000000000000 2572783498794789 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2572783498794789/2500000000000000 : ℝ)) (X := (58443852159113924597/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(150196993095903/6347200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(140937002083253/6347200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (3967/6250 : ℝ)) (alpha := (150196993095903/6347200000000000 : ℝ)) (beta := (140937002083253/6347200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3967/6250 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(150196993095903/6347200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(140937002083253/6347200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-15649883/80000000 : ℝ)*X 0 0+(2502122033/5000000000 : ℝ)*X 0 1+(314701077/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((888746291/2000000000 : ℝ)*X 1 0+(-174779477/1250000000 : ℝ)*X 1 1+(300324227/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4461487547/10000000000 : ℝ)*X 2 0+(6003828571/10000000000 : ℝ)*X 2 1+(-275794901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((7170449463/10000000000 : ℝ)*X 0 0+(36293601/156250000 : ℝ)*X 0 1+(1138854401/5000000000 : ℝ)*X 0 2+(7170449463/10000000000 : ℝ)*X 1 0+(36293601/156250000 : ℝ)*X 1 1+(1138854401/5000000000 : ℝ)*X 1 2+(7170449463/10000000000 : ℝ)*X 2 0+(36293601/156250000 : ℝ)*X 2 1+(1138854401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1921862269/10000000000 : ℝ)*X 0 0+(1058702851/2500000000 : ℝ)*X 0 1+(5805557891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4231130717/10000000000 : ℝ)*X 1 0+(-236619789/2000000000 : ℝ)*X 1 1+(6355800561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4248966939/10000000000 : ℝ)*X 2 0+(418420299/625000000 : ℝ)*X 2 1+(-79320487/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((7038301841/10000000000 : ℝ)*X 0 0+(67947459/200000000 : ℝ)*X 0 1+(1261900647/10000000000 : ℝ)*X 0 2+(7038301841/10000000000 : ℝ)*X 1 0+(67947459/200000000 : ℝ)*X 1 1+(1261900647/10000000000 : ℝ)*X 1 2+(7038301841/10000000000 : ℝ)*X 2 0+(67947459/200000000 : ℝ)*X 2 1+(1261900647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-604273189/5000000000 : ℝ)*X 0 0+(4867086699/10000000000 : ℝ)*X 0 1+(5740531413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4179903683/10000000000 : ℝ)*X 1 0+(-243596801/2000000000 : ℝ)*X 1 1+(3189187757/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5235124601/10000000000 : ℝ)*X 2 0+(229016561/400000000 : ℝ)*X 2 1+(-699594751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8051142257/10000000000 : ℝ)*X 0 0+(1097942633/5000000000 : ℝ)*X 0 1+(1191337393/10000000000 : ℝ)*X 0 2+(8051142257/10000000000 : ℝ)*X 1 0+(1097942633/5000000000 : ℝ)*X 1 1+(1191337393/10000000000 : ℝ)*X 1 2+(8051142257/10000000000 : ℝ)*X 2 0+(1097942633/5000000000 : ℝ)*X 2 1+(1191337393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1104720797/10000000000 : ℝ)*X 0 0+(1061709537/2000000000 : ℝ)*X 0 1+(2690595371/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((42568977/80000000 : ℝ)*X 1 0+(-408732881/5000000000 : ℝ)*X 1 1+(5564767573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4151852601/10000000000 : ℝ)*X 2 0+(6561299377/10000000000 : ℝ)*X 2 1+(-985828767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2048631943/2500000000 : ℝ)*X 0 0+(1601341353/10000000000 : ℝ)*X 0 1+(1615735793/10000000000 : ℝ)*X 0 2+(2048631943/2500000000 : ℝ)*X 1 0+(1601341353/10000000000 : ℝ)*X 1 1+(1615735793/10000000000 : ℝ)*X 1 2+(2048631943/2500000000 : ℝ)*X 2 0+(1601341353/10000000000 : ℝ)*X 2 1+(1615735793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((27003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2308860994119684898875679848441/239399239816100000000000000000000000 : ℝ) := by norm_num
    linear_combination (113150413807/500000000000 : ℝ)*(base49) + (1119725660697/1000000000000 : ℝ)*(base59) + (1632909457227/250000000000 : ℝ)*(major_s1_0) + (1632909457227/250000000000 : ℝ)*(major_s1_1) + (1632909457227/250000000000 : ℝ)*(major_s1_2) + (200999547/1000000000000 : ℝ)*(sp_s1_0) + (126337/25000000000 : ℝ)*(sp_s1_6) + (989643644983/100000000000 : ℝ)*(sp_s1_7) + (4948313873493/500000000000 : ℝ)*(sp_s1_8) + (9896027888689/1000000000000 : ℝ)*(sp_s1_9) + (49478427367/15625000000 : ℝ)*(sp_s1_13) + (10588661/1000000000000 : ℝ)*(sp_s1_14) + (5072763/250000000000 : ℝ)*(sp_s1_22) + (12402987/20000000000 : ℝ)*(sp_s1_23) + (395828050621/125000000000 : ℝ)*(f.failure) + (9896648038039/1000000000000 : ℝ)*(f.sum) + (8213938000621996023/103311787600000000000000000000000 : ℝ)*base63 + (1737433649111489/1586800000000000000000000000 : ℝ)*base65 + (2825540469216911/3255350000000000000000000000 : ℝ)*base67 + (1216785699786181/1586800000000000000000000000 : ℝ)*base69 + (43582494359554219931/102956344400000000000000000000000 : ℝ)*base71 + (1260023094088147/1622075000000000000000000000 : ℝ)*base73 + (1049965375710281/3255350000000000000000000000 : ℝ)*base75 + (10641968007677/101379687500000000000000000 : ℝ)*base77 + (3460708609758818269/15086919575000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1887/2500000000000000 : ℝ)*base86 + (1887/2500000000000000 : ℝ)*base88 + (1887/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33093/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33093/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (80273721679722150806422011/6034767830000000000000000000000 : ℝ) := by norm_num
    linear_combination (200327/1000000000000 : ℝ)*(base39) + (152425734827/500000000000 : ℝ)*(base49) + (520832413447/1000000000000 : ℝ)*(base59) + (636197505389/100000000000 : ℝ)*(major_s1_0) + (636197505389/100000000000 : ℝ)*(major_s1_1) + (636197505389/100000000000 : ℝ)*(major_s1_2) + (2742611/125000000000 : ℝ)*(sp_s1_1) + (7444421/250000000000 : ℝ)*(sp_s1_2) + (14316353/200000000000 : ℝ)*(sp_s1_7) + (2409876111081/250000000000 : ℝ)*(sp_s1_14) + (9639554085201/1000000000000 : ℝ)*(sp_s1_15) + (1927909249681/200000000000 : ℝ)*(sp_s1_16) + (1542140064561/500000000000 : ℝ)*(sp_s1_20) + (5594913/62500000000 : ℝ)*(sp_s1_27) + (308436964773/100000000000 : ℝ)*(f.failure) + (9639576026089/1000000000000 : ℝ)*(f.sum) + (1186912734470693369/41324715040000000000000000000000 : ℝ)*base63 + (183995644499281/634720000000000000000000000 : ℝ)*base64 + (133173143508113/651070000000000000000000000 : ℝ)*base66 + (211522628466749/634720000000000000000000000 : ℝ)*base68 + (1514107407079603709/41182537760000000000000000000000 : ℝ)*base71 + (130346231550967/162207500000000000000000000 : ℝ)*base72 + (44289195486229/130214000000000000000000000 : ℝ)*base74 + (55005323211889/162207500000000000000000000 : ℝ)*base76 + (1920329798616244607/6034767830000000000000000000000 : ℝ)*base78 + (569/2000000000000000 : ℝ)*base87 + (569/2000000000000000 : ℝ)*base89 + (569/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31629/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31629/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3906368528822742022316517/424983650000000000000000000000 : ℝ) := by norm_num
    linear_combination (50940668931/200000000000 : ℝ)*(base40) + (69220266973/500000000000 : ℝ)*(base49) + (532700416461/1000000000000 : ℝ)*(base59) + (5559670192367/1000000000000 : ℝ)*(major_s1_0) + (5559670192367/1000000000000 : ℝ)*(major_s1_1) + (5559670192367/1000000000000 : ℝ)*(major_s1_2) + (4830523/200000000000 : ℝ)*(sp_s1_0) + (3787223/125000000000 : ℝ)*(sp_s1_2) + (21219283/1000000000000 : ℝ)*(sp_s1_16) + (135434161/1000000000000 : ℝ)*(sp_s1_20) + (4211955764179/500000000000 : ℝ)*(sp_s1_21) + (8423935680973/1000000000000 : ℝ)*(sp_s1_22) + (8423884163907/1000000000000 : ℝ)*(sp_s1_23) + (539053241131/200000000000 : ℝ)*(sp_s1_27) + (336925204977/125000000000 : ℝ)*(f.failure) + (8423935680973/1000000000000 : ℝ)*(f.sum) + (2298893346800283333/5820382400000000000000000000000 : ℝ)*base63 + (3885719509943771/6347200000000000000000000000 : ℝ)*base64 + (35766185499161/45850000000000000000000000 : ℝ)*base66 + (1642211254292239/6347200000000000000000000000 : ℝ)*base68 + (110449667007506490191/411825377600000000000000000000000 : ℝ)*base71 + (2664929362513419/3244150000000000000000000000 : ℝ)*base72 + (31722039066951/45850000000000000000000000 : ℝ)*base74 + (5853143002950753/6488300000000000000000000000 : ℝ)*base76 + (130468577603512123/424983650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1319/2500000000000000 : ℝ)*base86 + (1319/2500000000000000 : ℝ)*base88 + (1319/2500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((64883/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64883/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65107/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(65107/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3967/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3967/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33093/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33093/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31629/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31629/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c326053_s1 p hpa hpb X hX hprev0

#print axioms solution
