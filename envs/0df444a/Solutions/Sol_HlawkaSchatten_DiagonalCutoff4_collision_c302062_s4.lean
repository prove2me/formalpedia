-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302062_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:07.562709+00:00
-- url     : https://prove2.me/submissions/7b581e2b-492b-4980-b144-50996265ad01

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
theorem collision_support_c302062_s4_s4_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036769631/5000000000 : ℝ)*x 0 + (305411679/625000000 : ℝ)*x 1 + (-726411891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036769631/5000000000 : ℝ)^131 ≤ (12469572952943/100000000000000 : ℝ)^99 := by
    have hnat : (1036769631 : ℕ)^131*100000000000000^99 ≤ 12469572952943^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036769631 5000000000 12469572952943 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305411679/625000000 : ℝ)^131 ≤ (1938439239667/5000000000000 : ℝ)^99 := by
    have hnat : (305411679 : ℕ)^131*5000000000000^99 ≤ 1938439239667^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305411679 625000000 1938439239667 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (726411891/1250000000 : ℝ)^131 ≤ (12190410561689/25000000000000 : ℝ)^99 := by
    have hnat : (726411891 : ℕ)^131*25000000000000^99 ≤ 12190410561689^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726411891 1250000000 12190410561689 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036769631/5000000000 : ℝ), (305411679/625000000 : ℝ), (-726411891/1250000000 : ℝ)] ![(12469572952943/100000000000000 : ℝ), (1938439239667/5000000000000 : ℝ), (12190410561689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036769631/5000000000 : ℝ)|^131 ≤ (12469572952943/100000000000000 : ℝ)^99
        have hw : |(-1036769631/5000000000 : ℝ)|=(1036769631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(305411679/625000000 : ℝ)|^131 ≤ (1938439239667/5000000000000 : ℝ)^99
        have hw : |(305411679/625000000 : ℝ)|=(305411679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-726411891/1250000000 : ℝ)|^131 ≤ (12190410561689/25000000000000 : ℝ)^99
        have hw : |(-726411891/1250000000 : ℝ)|=(726411891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2443693553/5000000000 : ℝ)*x 0 + (-1039774517/5000000000 : ℝ)*x 1 + (-2903114281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2443693553/5000000000 : ℝ)^131 ≤ (775543721483/2000000000000 : ℝ)^99 := by
    have hnat : (2443693553 : ℕ)^131*2000000000000^99 ≤ 775543721483^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2443693553 5000000000 775543721483 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039774517/5000000000 : ℝ)^131 ≤ (2503483592901/20000000000000 : ℝ)^99 := by
    have hnat : (1039774517 : ℕ)^131*20000000000000^99 ≤ 2503483592901^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039774517 5000000000 2503483592901 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2903114281/5000000000 : ℝ)^131 ≤ (9741079188623/20000000000000 : ℝ)^99 := by
    have hnat : (2903114281 : ℕ)^131*20000000000000^99 ≤ 9741079188623^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2903114281 5000000000 9741079188623 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2443693553/5000000000 : ℝ), (-1039774517/5000000000 : ℝ), (-2903114281/5000000000 : ℝ)] ![(775543721483/2000000000000 : ℝ), (2503483592901/20000000000000 : ℝ), (9741079188623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2443693553/5000000000 : ℝ)|^131 ≤ (775543721483/2000000000000 : ℝ)^99
        have hw : |(2443693553/5000000000 : ℝ)|=(2443693553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039774517/5000000000 : ℝ)|^131 ≤ (2503483592901/20000000000000 : ℝ)^99
        have hw : |(-1039774517/5000000000 : ℝ)|=(1039774517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2903114281/5000000000 : ℝ)|^131 ≤ (9741079188623/20000000000000 : ℝ)^99
        have hw : |(-2903114281/5000000000 : ℝ)|=(2903114281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1038206373/2000000000 : ℝ)*x 0 + (2596062927/5000000000 : ℝ)*x 1 + (2502829403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038206373/2000000000 : ℝ)^131 ≤ (41996634157071/100000000000000 : ℝ)^99 := by
    have hnat : (1038206373 : ℕ)^131*100000000000000^99 ≤ 41996634157071^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038206373 2000000000 41996634157071 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596062927/5000000000 : ℝ)^131 ≤ (42008345983773/100000000000000 : ℝ)^99 := by
    have hnat : (2596062927 : ℕ)^131*100000000000000^99 ≤ 42008345983773^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596062927 5000000000 42008345983773 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502829403/10000000000 : ℝ)^131 ≤ (7997509921911/50000000000000 : ℝ)^99 := by
    have hnat : (2502829403 : ℕ)^131*50000000000000^99 ≤ 7997509921911^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502829403 10000000000 7997509921911 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038206373/2000000000 : ℝ), (2596062927/5000000000 : ℝ), (2502829403/10000000000 : ℝ)] ![(41996634157071/100000000000000 : ℝ), (42008345983773/100000000000000 : ℝ), (7997509921911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038206373/2000000000 : ℝ)|^131 ≤ (41996634157071/100000000000000 : ℝ)^99
        have hw : |(1038206373/2000000000 : ℝ)|=(1038206373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596062927/5000000000 : ℝ)|^131 ≤ (42008345983773/100000000000000 : ℝ)^99
        have hw : |(2596062927/5000000000 : ℝ)|=(2596062927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502829403/10000000000 : ℝ)|^131 ≤ (7997509921911/50000000000000 : ℝ)^99
        have hw : |(2502829403/10000000000 : ℝ)|=(2502829403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-82832703/500000000 : ℝ)*x 0 + (856230833/2000000000 : ℝ)*x 1 + (-6641928887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82832703/500000000 : ℝ)^131 ≤ (4632680225833/50000000000000 : ℝ)^99 := by
    have hnat : (82832703 : ℕ)^131*50000000000000^99 ≤ 4632680225833^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82832703 500000000 4632680225833 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856230833/2000000000 : ℝ)^131 ≤ (8135971880443/25000000000000 : ℝ)^99 := by
    have hnat : (856230833 : ℕ)^131*25000000000000^99 ≤ 8135971880443^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856230833 2000000000 8135971880443 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6641928887/10000000000 : ℝ)^131 ≤ (58190752020697/100000000000000 : ℝ)^99 := by
    have hnat : (6641928887 : ℕ)^131*100000000000000^99 ≤ 58190752020697^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6641928887 10000000000 58190752020697 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82832703/500000000 : ℝ), (856230833/2000000000 : ℝ), (-6641928887/10000000000 : ℝ)] ![(4632680225833/50000000000000 : ℝ), (8135971880443/25000000000000 : ℝ), (58190752020697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82832703/500000000 : ℝ)|^131 ≤ (4632680225833/50000000000000 : ℝ)^99
        have hw : |(-82832703/500000000 : ℝ)|=(82832703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(856230833/2000000000 : ℝ)|^131 ≤ (8135971880443/25000000000000 : ℝ)^99
        have hw : |(856230833/2000000000 : ℝ)|=(856230833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6641928887/10000000000 : ℝ)|^131 ≤ (58190752020697/100000000000000 : ℝ)^99
        have hw : |(-6641928887/10000000000 : ℝ)|=(6641928887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4709912909/10000000000 : ℝ)*x 0 + (-1233540171/10000000000 : ℝ)*x 1 + (-652190069/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4709912909/10000000000 : ℝ)^131 ≤ (36924963026669/100000000000000 : ℝ)^99 := by
    have hnat : (4709912909 : ℕ)^131*100000000000000^99 ≤ 36924963026669^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4709912909 10000000000 36924963026669 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233540171/10000000000 : ℝ)^131 ≤ (3135845593491/50000000000000 : ℝ)^99 := by
    have hnat : (1233540171 : ℕ)^131*50000000000000^99 ≤ 3135845593491^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233540171 10000000000 3135845593491 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652190069/1000000000 : ℝ)^131 ≤ (11360669155429/20000000000000 : ℝ)^99 := by
    have hnat : (652190069 : ℕ)^131*20000000000000^99 ≤ 11360669155429^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652190069 1000000000 11360669155429 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4709912909/10000000000 : ℝ), (-1233540171/10000000000 : ℝ), (-652190069/1000000000 : ℝ)] ![(36924963026669/100000000000000 : ℝ), (3135845593491/50000000000000 : ℝ), (11360669155429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4709912909/10000000000 : ℝ)|^131 ≤ (36924963026669/100000000000000 : ℝ)^99
        have hw : |(4709912909/10000000000 : ℝ)|=(4709912909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1233540171/10000000000 : ℝ)|^131 ≤ (3135845593491/50000000000000 : ℝ)^99
        have hw : |(-1233540171/10000000000 : ℝ)|=(1233540171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-652190069/1000000000 : ℝ)|^131 ≤ (11360669155429/20000000000000 : ℝ)^99
        have hw : |(-652190069/1000000000 : ℝ)|=(652190069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4810204653/10000000000 : ℝ)*x 0 + (3152392381/5000000000 : ℝ)*x 1 + (144274711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4810204653/10000000000 : ℝ)^131 ≤ (18984472989637/50000000000000 : ℝ)^99 := by
    have hnat : (4810204653 : ℕ)^131*50000000000000^99 ≤ 18984472989637^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810204653 10000000000 18984472989637 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3152392381/5000000000 : ℝ)^131 ≤ (6789334905541/12500000000000 : ℝ)^99 := by
    have hnat : (3152392381 : ℕ)^131*12500000000000^99 ≤ 6789334905541^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3152392381 5000000000 6789334905541 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144274711/1000000000 : ℝ)^131 ≤ (1929093691783/25000000000000 : ℝ)^99 := by
    have hnat : (144274711 : ℕ)^131*25000000000000^99 ≤ 1929093691783^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144274711 1000000000 1929093691783 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4810204653/10000000000 : ℝ), (3152392381/5000000000 : ℝ), (144274711/1000000000 : ℝ)] ![(18984472989637/50000000000000 : ℝ), (6789334905541/12500000000000 : ℝ), (1929093691783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4810204653/10000000000 : ℝ)|^131 ≤ (18984472989637/50000000000000 : ℝ)^99
        have hw : |(4810204653/10000000000 : ℝ)|=(4810204653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3152392381/5000000000 : ℝ)|^131 ≤ (6789334905541/12500000000000 : ℝ)^99
        have hw : |(3152392381/5000000000 : ℝ)|=(3152392381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(144274711/1000000000 : ℝ)|^131 ≤ (1929093691783/25000000000000 : ℝ)^99
        have hw : |(144274711/1000000000 : ℝ)|=(144274711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2538788671/5000000000 : ℝ)*x 0 + (3195622507/5000000000 : ℝ)*x 1 + (-13489313/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2538788671/5000000000 : ℝ)^131 ≤ (10196596599499/25000000000000 : ℝ)^99 := by
    have hnat : (2538788671 : ℕ)^131*25000000000000^99 ≤ 10196596599499^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538788671 5000000000 10196596599499 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3195622507/5000000000 : ℝ)^131 ≤ (55302454324507/100000000000000 : ℝ)^99 := by
    have hnat : (3195622507 : ℕ)^131*100000000000000^99 ≤ 55302454324507^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195622507 5000000000 55302454324507 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13489313/156250000 : ℝ)^131 ≤ (61111863477/1562500000000 : ℝ)^99 := by
    have hnat : (13489313 : ℕ)^131*1562500000000^99 ≤ 61111863477^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13489313 156250000 61111863477 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2538788671/5000000000 : ℝ), (3195622507/5000000000 : ℝ), (-13489313/156250000 : ℝ)] ![(10196596599499/25000000000000 : ℝ), (55302454324507/100000000000000 : ℝ), (61111863477/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2538788671/5000000000 : ℝ)|^131 ≤ (10196596599499/25000000000000 : ℝ)^99
        have hw : |(2538788671/5000000000 : ℝ)|=(2538788671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3195622507/5000000000 : ℝ)|^131 ≤ (55302454324507/100000000000000 : ℝ)^99
        have hw : |(3195622507/5000000000 : ℝ)|=(3195622507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13489313/156250000 : ℝ)|^131 ≤ (61111863477/1562500000000 : ℝ)^99
        have hw : |(-13489313/156250000 : ℝ)|=(13489313/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-28779433/250000000 : ℝ)*x 0 + (4638488861/10000000000 : ℝ)*x 1 + (-1658320141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28779433/250000000 : ℝ)^131 ≤ (2861824841597/50000000000000 : ℝ)^99 := by
    have hnat : (28779433 : ℕ)^131*50000000000000^99 ≤ 2861824841597^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28779433 250000000 2861824841597 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4638488861/10000000000 : ℝ)^131 ≤ (36185837189099/100000000000000 : ℝ)^99 := by
    have hnat : (4638488861 : ℕ)^131*100000000000000^99 ≤ 36185837189099^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4638488861 10000000000 36185837189099 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1658320141/2500000000 : ℝ)^131 ≤ (58090513113667/100000000000000 : ℝ)^99 := by
    have hnat : (1658320141 : ℕ)^131*100000000000000^99 ≤ 58090513113667^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658320141 2500000000 58090513113667 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28779433/250000000 : ℝ), (4638488861/10000000000 : ℝ), (-1658320141/2500000000 : ℝ)] ![(2861824841597/50000000000000 : ℝ), (36185837189099/100000000000000 : ℝ), (58090513113667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28779433/250000000 : ℝ)|^131 ≤ (2861824841597/50000000000000 : ℝ)^99
        have hw : |(-28779433/250000000 : ℝ)|=(28779433/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4638488861/10000000000 : ℝ)|^131 ≤ (36185837189099/100000000000000 : ℝ)^99
        have hw : |(4638488861/10000000000 : ℝ)|=(4638488861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1658320141/2500000000 : ℝ)|^131 ≤ (58090513113667/100000000000000 : ℝ)^99
        have hw : |(-1658320141/2500000000 : ℝ)|=(1658320141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4370022603/10000000000 : ℝ)*x 0 + (-433551031/2500000000 : ℝ)*x 1 + (-3257144853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370022603/10000000000 : ℝ)^131 ≤ (3344077924933/10000000000000 : ℝ)^99 := by
    have hnat : (4370022603 : ℕ)^131*10000000000000^99 ≤ 3344077924933^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370022603 10000000000 3344077924933 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433551031/2500000000 : ℝ)^131 ≤ (4921786986427/50000000000000 : ℝ)^99 := by
    have hnat : (433551031 : ℕ)^131*50000000000000^99 ≤ 4921786986427^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433551031 2500000000 4921786986427 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3257144853/5000000000 : ℝ)^131 ≤ (28357823382003/50000000000000 : ℝ)^99 := by
    have hnat : (3257144853 : ℕ)^131*50000000000000^99 ≤ 28357823382003^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3257144853 5000000000 28357823382003 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370022603/10000000000 : ℝ), (-433551031/2500000000 : ℝ), (-3257144853/5000000000 : ℝ)] ![(3344077924933/10000000000000 : ℝ), (4921786986427/50000000000000 : ℝ), (28357823382003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370022603/10000000000 : ℝ)|^131 ≤ (3344077924933/10000000000000 : ℝ)^99
        have hw : |(4370022603/10000000000 : ℝ)|=(4370022603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433551031/2500000000 : ℝ)|^131 ≤ (4921786986427/50000000000000 : ℝ)^99
        have hw : |(-433551031/2500000000 : ℝ)|=(433551031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3257144853/5000000000 : ℝ)|^131 ≤ (28357823382003/50000000000000 : ℝ)^99
        have hw : |(-3257144853/5000000000 : ℝ)|=(3257144853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (385880683/625000000 : ℝ)*x 0 + (494658073/1000000000 : ℝ)*x 1 + (1450358177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385880683/625000000 : ℝ)^131 ≤ (26414929543479/50000000000000 : ℝ)^99 := by
    have hnat : (385880683 : ℕ)^131*50000000000000^99 ≤ 26414929543479^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385880683 625000000 26414929543479 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494658073/1000000000 : ℝ)^131 ≤ (39399855497393/100000000000000 : ℝ)^99 := by
    have hnat : (494658073 : ℕ)^131*100000000000000^99 ≤ 39399855497393^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494658073 1000000000 39399855497393 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1450358177/10000000000 : ℝ)^131 ≤ (971285674893/12500000000000 : ℝ)^99 := by
    have hnat : (1450358177 : ℕ)^131*12500000000000^99 ≤ 971285674893^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450358177 10000000000 971285674893 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(385880683/625000000 : ℝ), (494658073/1000000000 : ℝ), (1450358177/10000000000 : ℝ)] ![(26414929543479/50000000000000 : ℝ), (39399855497393/100000000000000 : ℝ), (971285674893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(385880683/625000000 : ℝ)|^131 ≤ (26414929543479/50000000000000 : ℝ)^99
        have hw : |(385880683/625000000 : ℝ)|=(385880683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(494658073/1000000000 : ℝ)|^131 ≤ (39399855497393/100000000000000 : ℝ)^99
        have hw : |(494658073/1000000000 : ℝ)|=(494658073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1450358177/10000000000 : ℝ)|^131 ≤ (971285674893/12500000000000 : ℝ)^99
        have hw : |(1450358177/10000000000 : ℝ)|=(1450358177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (82969501/125000000 : ℝ)*x 0 + (4798388141/10000000000 : ℝ)*x 1 + (-880469103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82969501/125000000 : ℝ)^131 ≤ (29070054912227/50000000000000 : ℝ)^99 := by
    have hnat : (82969501 : ℕ)^131*50000000000000^99 ≤ 29070054912227^99*125000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82969501 125000000 29070054912227 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4798388141/10000000000 : ℝ)^131 ≤ (37845573629693/100000000000000 : ℝ)^99 := by
    have hnat : (4798388141 : ℕ)^131*100000000000000^99 ≤ 37845573629693^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798388141 10000000000 37845573629693 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880469103/10000000000 : ℝ)^131 ≤ (1003579133129/25000000000000 : ℝ)^99 := by
    have hnat : (880469103 : ℕ)^131*25000000000000^99 ≤ 1003579133129^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880469103 10000000000 1003579133129 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82969501/125000000 : ℝ), (4798388141/10000000000 : ℝ), (-880469103/10000000000 : ℝ)] ![(29070054912227/50000000000000 : ℝ), (37845573629693/100000000000000 : ℝ), (1003579133129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82969501/125000000 : ℝ)|^131 ≤ (29070054912227/50000000000000 : ℝ)^99
        have hw : |(82969501/125000000 : ℝ)|=(82969501/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4798388141/10000000000 : ℝ)|^131 ≤ (37845573629693/100000000000000 : ℝ)^99
        have hw : |(4798388141/10000000000 : ℝ)|=(4798388141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880469103/10000000000 : ℝ)|^131 ≤ (1003579133129/25000000000000 : ℝ)^99
        have hw : |(-880469103/10000000000 : ℝ)|=(880469103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-11185037/125000000 : ℝ)*x 0 + (5443049169/10000000000 : ℝ)*x 1 + (-1205624797/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11185037/125000000 : ℝ)^131 ≤ (410101944113/10000000000000 : ℝ)^99 := by
    have hnat : (11185037 : ℕ)^131*10000000000000^99 ≤ 410101944113^99*125000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11185037 125000000 410101944113 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443049169/10000000000 : ℝ)^131 ≤ (8943096815253/20000000000000 : ℝ)^99 := by
    have hnat : (5443049169 : ℕ)^131*20000000000000^99 ≤ 8943096815253^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443049169 10000000000 8943096815253 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205624797/2000000000 : ℝ)^131 ≤ (51183496474613/100000000000000 : ℝ)^99 := by
    have hnat : (1205624797 : ℕ)^131*100000000000000^99 ≤ 51183496474613^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205624797 2000000000 51183496474613 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11185037/125000000 : ℝ), (5443049169/10000000000 : ℝ), (-1205624797/2000000000 : ℝ)] ![(410101944113/10000000000000 : ℝ), (8943096815253/20000000000000 : ℝ), (51183496474613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11185037/125000000 : ℝ)|^131 ≤ (410101944113/10000000000000 : ℝ)^99
        have hw : |(-11185037/125000000 : ℝ)|=(11185037/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443049169/10000000000 : ℝ)|^131 ≤ (8943096815253/20000000000000 : ℝ)^99
        have hw : |(5443049169/10000000000 : ℝ)|=(5443049169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1205624797/2000000000 : ℝ)|^131 ≤ (51183496474613/100000000000000 : ℝ)^99
        have hw : |(-1205624797/2000000000 : ℝ)|=(1205624797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (765535327/1250000000 : ℝ)*x 0 + (-1581293507/10000000000 : ℝ)*x 1 + (-4910646621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765535327/1250000000 : ℝ)^131 ≤ (52266640842483/100000000000000 : ℝ)^99 := by
    have hnat : (765535327 : ℕ)^131*100000000000000^99 ≤ 52266640842483^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765535327 1250000000 52266640842483 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1581293507/10000000000 : ℝ)^131 ≤ (8711790703811/100000000000000 : ℝ)^99 := by
    have hnat : (1581293507 : ℕ)^131*100000000000000^99 ≤ 8711790703811^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581293507 10000000000 8711790703811 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4910646621/10000000000 : ℝ)^131 ≤ (39021568435833/100000000000000 : ℝ)^99 := by
    have hnat : (4910646621 : ℕ)^131*100000000000000^99 ≤ 39021568435833^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4910646621 10000000000 39021568435833 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(765535327/1250000000 : ℝ), (-1581293507/10000000000 : ℝ), (-4910646621/10000000000 : ℝ)] ![(52266640842483/100000000000000 : ℝ), (8711790703811/100000000000000 : ℝ), (39021568435833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(765535327/1250000000 : ℝ)|^131 ≤ (52266640842483/100000000000000 : ℝ)^99
        have hw : |(765535327/1250000000 : ℝ)|=(765535327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1581293507/10000000000 : ℝ)|^131 ≤ (8711790703811/100000000000000 : ℝ)^99
        have hw : |(-1581293507/10000000000 : ℝ)|=(1581293507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4910646621/10000000000 : ℝ)|^131 ≤ (39021568435833/100000000000000 : ℝ)^99
        have hw : |(-4910646621/10000000000 : ℝ)|=(4910646621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2293013539/5000000000 : ℝ)*x 0 + (5751140459/10000000000 : ℝ)*x 1 + (2534084577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2293013539/5000000000 : ℝ)^131 ≤ (17822638134893/50000000000000 : ℝ)^99 := by
    have hnat : (2293013539 : ℕ)^131*50000000000000^99 ≤ 17822638134893^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293013539 5000000000 17822638134893 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5751140459/10000000000 : ℝ)^131 ≤ (9618972632189/20000000000000 : ℝ)^99 := by
    have hnat : (5751140459 : ℕ)^131*20000000000000^99 ≤ 9618972632189^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5751140459 10000000000 9618972632189 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2534084577/10000000000 : ℝ)^131 ≤ (8129930275211/50000000000000 : ℝ)^99 := by
    have hnat : (2534084577 : ℕ)^131*50000000000000^99 ≤ 8129930275211^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534084577 10000000000 8129930275211 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2293013539/5000000000 : ℝ), (5751140459/10000000000 : ℝ), (2534084577/10000000000 : ℝ)] ![(17822638134893/50000000000000 : ℝ), (9618972632189/20000000000000 : ℝ), (8129930275211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2293013539/5000000000 : ℝ)|^131 ≤ (17822638134893/50000000000000 : ℝ)^99
        have hw : |(2293013539/5000000000 : ℝ)|=(2293013539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5751140459/10000000000 : ℝ)|^131 ≤ (9618972632189/20000000000000 : ℝ)^99
        have hw : |(5751140459/10000000000 : ℝ)|=(5751140459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2534084577/10000000000 : ℝ)|^131 ≤ (8129930275211/50000000000000 : ℝ)^99
        have hw : |(2534084577/10000000000 : ℝ)|=(2534084577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302062_s4_s4_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3408209799/5000000000 : ℝ)*x 0 + (4495106389/10000000000 : ℝ)*x 1 + (-52476687/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3408209799/5000000000 : ℝ)^131 ≤ (7527770164921/12500000000000 : ℝ)^99 := by
    have hnat : (3408209799 : ℕ)^131*12500000000000^99 ≤ 7527770164921^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408209799 5000000000 7527770164921 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495106389/10000000000 : ℝ)^131 ≤ (8678293201951/25000000000000 : ℝ)^99 := by
    have hnat : (4495106389 : ℕ)^131*25000000000000^99 ≤ 8678293201951^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495106389 10000000000 8678293201951 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52476687/500000000 : ℝ)^131 ≤ (1266166464779/25000000000000 : ℝ)^99 := by
    have hnat : (52476687 : ℕ)^131*25000000000000^99 ≤ 1266166464779^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52476687 500000000 1266166464779 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3408209799/5000000000 : ℝ), (4495106389/10000000000 : ℝ), (-52476687/500000000 : ℝ)] ![(7527770164921/12500000000000 : ℝ), (8678293201951/25000000000000 : ℝ), (1266166464779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3408209799/5000000000 : ℝ)|^131 ≤ (7527770164921/12500000000000 : ℝ)^99
        have hw : |(3408209799/5000000000 : ℝ)|=(3408209799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495106389/10000000000 : ℝ)|^131 ≤ (8678293201951/25000000000000 : ℝ)^99
        have hw : |(4495106389/10000000000 : ℝ)|=(4495106389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52476687/500000000 : ℝ)|^131 ≤ (1266166464779/25000000000000 : ℝ)^99
        have hw : |(-52476687/500000000 : ℝ)|=(52476687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302062_s4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((66511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66761/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66761/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4831/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4831/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5403/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5403/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8701/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8701/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28189/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28189/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (66511/100000 : ℝ) ^ (65/16 : ℝ) ≤ (9538382999027023073/50000000000000000000 : ℝ) := by
    have hpowers : (66511/100000 : ℝ)^65 ≤ (9538382999027023073/50000000000000000000 : ℝ)^16 := by
      have hnat : (66511 : ℕ)^65*50000000000000000000^16 ≤ 9538382999027023073^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66511 100000 9538382999027023073 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66511/100000 : ℝ)) (X := (9538382999027023073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (59538382999027023073/50000000000000000000 : ℝ) ≤ (10439149455734153/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (59538382999027023073/50000000000000000000 : ℝ)^16 ≤ (10439149455734153/10000000000000000 : ℝ)^65 := by
      have hnat : (59538382999027023073 : ℕ)^16*10000000000000000^65 ≤ 10439149455734153^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59538382999027023073 50000000000000000000 10439149455734153 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10439149455734153/10000000000000000 : ℝ)) (X := (59538382999027023073/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (34538382999027023073/25000000000000000000 : ℝ) ≤ (10828059768020299/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (34538382999027023073/25000000000000000000 : ℝ)^16 ≤ (10828059768020299/10000000000000000 : ℝ)^65 := by
      have hnat : (34538382999027023073 : ℕ)^16*10000000000000000^65 ≤ 10828059768020299^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34538382999027023073 25000000000000000000 10828059768020299 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10828059768020299/10000000000000000 : ℝ)) (X := (34538382999027023073/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(439149455734153/6651100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(194455156143073/3325550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (66511/100000 : ℝ)) (alpha := (439149455734153/6651100000000000 : ℝ)) (beta := (194455156143073/3325550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (66511/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(439149455734153/6651100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(194455156143073/3325550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (66761/100000 : ℝ) ^ (65/16 : ℝ) ≤ (19369749764319478549/100000000000000000000 : ℝ) := by
    have hpowers : (66761/100000 : ℝ)^65 ≤ (19369749764319478549/100000000000000000000 : ℝ)^16 := by
      have hnat : (66761 : ℕ)^65*100000000000000000000^16 ≤ 19369749764319478549^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66761 100000 19369749764319478549 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66761/100000 : ℝ)) (X := (19369749764319478549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (119369749764319478549/100000000000000000000 : ℝ) ≤ (5222733046171877/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (119369749764319478549/100000000000000000000 : ℝ)^16 ≤ (5222733046171877/5000000000000000 : ℝ)^65 := by
      have hnat : (119369749764319478549 : ℕ)^16*5000000000000000^65 ≤ 5222733046171877^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119369749764319478549 100000000000000000000 5222733046171877 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5222733046171877/5000000000000000 : ℝ)) (X := (119369749764319478549/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (69369749764319478549/50000000000000000000 : ℝ) ≤ (2709836673601023/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (69369749764319478549/50000000000000000000 : ℝ)^16 ≤ (2709836673601023/2500000000000000 : ℝ)^65 := by
      have hnat : (69369749764319478549 : ℕ)^16*2500000000000000^65 ≤ 2709836673601023^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69369749764319478549 50000000000000000000 2709836673601023 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2709836673601023/2500000000000000 : ℝ)) (X := (69369749764319478549/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(222733046171877/3338050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(196940301030169/3338050000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (66761/100000 : ℝ)) (alpha := (222733046171877/3338050000000000 : ℝ)) (beta := (196940301030169/3338050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (66761/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(222733046171877/3338050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(196940301030169/3338050000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (4831/10000 : ℝ) ^ (65/16 : ℝ) ≤ (1040951416383509219/20000000000000000000 : ℝ) := by
    have hpowers : (4831/10000 : ℝ)^65 ≤ (1040951416383509219/20000000000000000000 : ℝ)^16 := by
      have hnat : (4831 : ℕ)^65*20000000000000000000^16 ≤ 1040951416383509219^16*10000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4831 10000 1040951416383509219 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4831/10000 : ℝ)) (X := (1040951416383509219/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (21040951416383509219/20000000000000000000 : ℝ) ≤ (2025135508914829/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (21040951416383509219/20000000000000000000 : ℝ)^16 ≤ (2025135508914829/2000000000000000 : ℝ)^65 := by
      have hnat : (21040951416383509219 : ℕ)^16*2000000000000000^65 ≤ 2025135508914829^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21040951416383509219 20000000000000000000 2025135508914829 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2025135508914829/2000000000000000 : ℝ)) (X := (21040951416383509219/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (11040951416383509219/10000000000000000000 : ℝ) ≤ (2561687940468639/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (11040951416383509219/10000000000000000000 : ℝ)^16 ≤ (2561687940468639/2500000000000000 : ℝ)^65 := by
      have hnat : (11040951416383509219 : ℕ)^16*2500000000000000^65 ≤ 2561687940468639^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11040951416383509219 10000000000000000000 2561687940468639 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2561687940468639/2500000000000000 : ℝ)) (X := (11040951416383509219/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(25135508914829/966200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(121074217300411/4831000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (4831/10000 : ℝ)) (alpha := (25135508914829/966200000000000 : ℝ)) (beta := (121074217300411/4831000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (4831/10000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(25135508914829/966200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(121074217300411/4831000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1036769631/5000000000 : ℝ)*X 0 0+(305411679/625000000 : ℝ)*X 0 1+(-726411891/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((2443693553/5000000000 : ℝ)*X 1 0+(-1039774517/5000000000 : ℝ)*X 1 1+(-2903114281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((1038206373/2000000000 : ℝ)*X 2 0+(2596062927/5000000000 : ℝ)*X 2 1+(2502829403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-82832703/500000000 : ℝ)*X 0 0+(856230833/2000000000 : ℝ)*X 0 1+(-6641928887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4709912909/10000000000 : ℝ)*X 1 0+(-1233540171/10000000000 : ℝ)*X 1 1+(-652190069/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4810204653/10000000000 : ℝ)*X 2 0+(3152392381/5000000000 : ℝ)*X 2 1+(144274711/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((2538788671/5000000000 : ℝ)*X 0 0+(3195622507/5000000000 : ℝ)*X 0 1+(-13489313/156250000 : ℝ)*X 0 2+(2538788671/5000000000 : ℝ)*X 1 0+(3195622507/5000000000 : ℝ)*X 1 1+(-13489313/156250000 : ℝ)*X 1 2+(2538788671/5000000000 : ℝ)*X 2 0+(3195622507/5000000000 : ℝ)*X 2 1+(-13489313/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-28779433/250000000 : ℝ)*X 0 0+(4638488861/10000000000 : ℝ)*X 0 1+(-1658320141/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4370022603/10000000000 : ℝ)*X 1 0+(-433551031/2500000000 : ℝ)*X 1 1+(-3257144853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((385880683/625000000 : ℝ)*X 2 0+(494658073/1000000000 : ℝ)*X 2 1+(1450358177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((82969501/125000000 : ℝ)*X 0 0+(4798388141/10000000000 : ℝ)*X 0 1+(-880469103/10000000000 : ℝ)*X 0 2+(82969501/125000000 : ℝ)*X 1 0+(4798388141/10000000000 : ℝ)*X 1 1+(-880469103/10000000000 : ℝ)*X 1 2+(82969501/125000000 : ℝ)*X 2 0+(4798388141/10000000000 : ℝ)*X 2 1+(-880469103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-11185037/125000000 : ℝ)*X 0 0+(5443049169/10000000000 : ℝ)*X 0 1+(-1205624797/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((765535327/1250000000 : ℝ)*X 1 0+(-1581293507/10000000000 : ℝ)*X 1 1+(-4910646621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((2293013539/5000000000 : ℝ)*X 2 0+(5751140459/10000000000 : ℝ)*X 2 1+(2534084577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((3408209799/5000000000 : ℝ)*X 0 0+(4495106389/10000000000 : ℝ)*X 0 1+(-52476687/500000000 : ℝ)*X 0 2+(3408209799/5000000000 : ℝ)*X 1 0+(4495106389/10000000000 : ℝ)*X 1 1+(-52476687/500000000 : ℝ)*X 1 2+(3408209799/5000000000 : ℝ)*X 2 0+(4495106389/10000000000 : ℝ)*X 2 1+(-52476687/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302062_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((5403/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5403/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (120325621204713681786421146649041/10725643373900500000000000000000000000 : ℝ) := by norm_num
    linear_combination (82129055377/1000000000000 : ℝ)*(base39) + (7104747/1000000000000 : ℝ)*(base49) + (136382202861/1000000000000 : ℝ)*(base60) + (4981942722893/1000000000000 : ℝ)*(major_s4_0) + (4981942722893/1000000000000 : ℝ)*(major_s4_1) + (4981942722893/1000000000000 : ℝ)*(major_s4_2) + (55677479/1000000000000 : ℝ)*(sp_s4_0) + (5446981/1000000000000 : ℝ)*(sp_s4_1) + (6624050790557/1000000000000 : ℝ)*(sp_s4_7) + (3311991016143/500000000000 : ℝ)*(sp_s4_8) + (1656002588089/250000000000 : ℝ)*(sp_s4_9) + (3339775238247/1000000000000 : ℝ)*(sp_s4_13) + (118988769/1000000000000 : ℝ)*(sp_s4_15) + (600723/6250000000 : ℝ)*(sp_s4_23) + (3339775238247/1000000000000 : ℝ)*(f.failure) + (1656026617009/250000000000 : ℝ)*(f.sum) + (21716632036522188739/64504478200000000000000000000000 : ℝ)*base62 + (2126481193610123/4831000000000000000000000000 : ℝ)*base65 + (404787775188677/834512500000000000000000000 : ℝ)*base66 + (31694581616877/966200000000000000000000000 : ℝ)*base69 + (29977363422307683543/321314641000000000000000000000000 : ℝ)*base71 + (2952458315423411/3325550000000000000000000000 : ℝ)*base72 + (928125155213651/3338050000000000000000000000 : ℝ)*base75 + (1494505697661129/6651100000000000000000000000 : ℝ)*base77 + (12510472830198522033/27752130443750000000000000000000 : ℝ)*base78 + (499/10000000000000000 : ℝ)*base87 + (499/10000000000000000 : ℝ)*base89 + (499/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8701/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8701/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33161541942116743125294718567467/5362821686950250000000000000000000000 : ℝ) := by norm_num
    linear_combination (82077839403/1000000000000 : ℝ)*(base39) + (78251/62500000000 : ℝ)*(base60) + (5021030013673/1000000000000 : ℝ)*(major_s4_0) + (5021030013673/1000000000000 : ℝ)*(major_s4_1) + (5021030013673/1000000000000 : ℝ)*(major_s4_2) + (236599/200000000000 : ℝ)*(sp_s4_0) + (2845657/200000000000 : ℝ)*(sp_s4_2) + (15453597/500000000000 : ℝ)*(sp_s4_7) + (18590301/1000000000000 : ℝ)*(sp_s4_8) + (1669011863223/250000000000 : ℝ)*(sp_s4_14) + (333803047639/50000000000 : ℝ)*(sp_s4_15) + (1669016328699/250000000000 : ℝ)*(sp_s4_16) + (841473337319/250000000000 : ℝ)*(sp_s4_20) + (4253689/50000000000 : ℝ)*(sp_s4_27) + (210373651441/62500000000 : ℝ)*(f.failure) + (3338039771541/500000000000 : ℝ)*(f.sum) + (31155846713310117441/64504478200000000000000000000000 : ℝ)*base63 + (125951928138197/4831000000000000000000000000 : ℝ)*base64 + (1187586515848293/3338050000000000000000000000 : ℝ)*base66 + (757731174262137/966200000000000000000000000 : ℝ)*base69 + (108536564491818536977/321314641000000000000000000000000 : ℝ)*base70 + (1574895586342981/3325550000000000000000000000 : ℝ)*base72 + (380452638156289/834512500000000000000000000 : ℝ)*base75 + (2542266546525309/6651100000000000000000000000 : ℝ)*base77 + (3714797167708200469/222017043550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (57/156250000000000 : ℝ)*base86 + (57/156250000000000 : ℝ)*base88 + (57/156250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28189/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28189/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22025944869662489221092904981179/2681410843475125000000000000000000000 : ℝ) := by norm_num
    linear_combination (3163597/500000000000 : ℝ)*(base11) + (608002944541/1000000000000 : ℝ)*(base39) + (422329/1000000000000 : ℝ)*(base40) + (90431/250000000000 : ℝ)*(base59) + (2038814874131/500000000000 : ℝ)*(major_s4_0) + (2038814874131/500000000000 : ℝ)*(major_s4_1) + (2038814874131/500000000000 : ℝ)*(major_s4_2) + (12207117/500000000000 : ℝ)*(sp_s4_0) + (206261/1000000000000 : ℝ)*(sp_s4_2) + (9408469/250000000000 : ℝ)*(sp_s4_9) + (2710840283327/500000000000 : ℝ)*(sp_s4_21) + (2710855654041/500000000000 : ℝ)*(sp_s4_22) + (677709183493/125000000000 : ℝ)*(sp_s4_23) + (2733545450333/1000000000000 : ℝ)*(sp_s4_27) + (2733545450333/1000000000000 : ℝ)*(f.failure) + (2710855654041/500000000000 : ℝ)*(f.sum) + (6032321876937494967/32252239100000000000000000000000 : ℝ)*base63 + (273939508662609/2415500000000000000000000000 : ℝ)*base64 + (74870774028711/417256250000000000000000000 : ℝ)*base67 + (47501956499661/483100000000000000000000000 : ℝ)*base68 + (59261995717414104069/160657320500000000000000000000000 : ℝ)*base70 + (271694982531617/415693750000000000000000000 : ℝ)*base73 + (1535046391705779/3338050000000000000000000000 : ℝ)*base75 + (16574501849801/1662775000000000000000000000 : ℝ)*base76 + (146436577254690205039/222017043550000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (2639/10000000000000000 : ℝ)*base86 + (2639/10000000000000000 : ℝ)*base88 + (2639/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((66511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66761/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66761/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4831/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4831/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5403/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5403/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8701/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8701/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-28189/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-28189/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302062_s4 p hpa hpb X hX hprev3

#print axioms solution
